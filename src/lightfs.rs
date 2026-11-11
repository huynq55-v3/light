// File: src/lightfs.rs — LightFS: định dạng đĩa + công cụ host (pack, sync, fsck, ghi file kiểu copy-on-write)
//
// Đơn vị: sector 512 byte; dữ liệu cấp phát theo khối 4KB (8 sector), mỗi file đúng 1 extent liên tục.
//
//   LBA 0       Header (không bao giờ ghi lại sau khi tạo): q0 "LIGHTFS1", q1 phiên bản, q2 tổng sector,
//               q3 số sector bảng (64), q4/q5 LBA vùng bảng A/B, q6 LBA vùng dữ liệu, q7 checksum(q0..q6)
//   LBA 1, 2    Bản ghi commit slot 0/1: q0 "LFSCOMIT", q1 thế hệ, q2 vùng bảng (0/1), q3 checksum bảng,
//               q7 checksum(q0..q6). Bản hợp lệ có thế hệ lớn nhất (và bảng khớp checksum) là trạng thái hiện tại.
//   LBA 8..71   Vùng bảng A — 256 mục x 128 byte
//   LBA 72..135 Vùng bảng B
//   LBA 136..   Khối dữ liệu (khối b = LBA 136 + 8b)
//
// Mục bảng (16 qword): q0 cờ (1 dùng, 2 thư mục, 4 App), q1 chỉ số thư mục cha, q2 kích thước byte,
// q3 khối đầu, q4 số khối, q5 checksum dữ liệu (trên ceil(size/512) sector), q6 thế hệ ghi, q7 dự trữ,
// q8..q15 tên (tối đa 63 byte ASCII in được, không có '/', kết thúc bằng 0). Mục 0 = thư mục gốc.
//
// Ghi an toàn khi mất điện (copy-on-write, mỗi thao tác là một giao dịch):
//   1. dữ liệu mới vào khối CÒN TRỐNG (không bao giờ ghi đè khối đang được bảng hiện tại dùng)
//   2. flush; bảng mới vào vùng KHÔNG hiện hành; flush
//   3. bản ghi commit thế hệ+1 vào slot (thế hệ+1) % 2; flush
// Mất điện trước bước 3 -> bảng cũ + dữ liệu cũ còn nguyên. Bản ghi commit nằm trọn 1 sector và có checksum, nên
// ghi dở dang thì bị bỏ qua và slot còn lại (thế hệ cũ) được dùng.
// Kernel (lit_program/os/lightfs.lit) cài đặt đúng giao thức này; `Fs` ở đây là bản tham chiếu dùng cho pack và test.
use std::collections::{BTreeMap, HashSet};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::Path;

pub const SECTOR: usize = 512;
pub const MAGIC: u64 = u64::from_le_bytes(*b"LIGHTFS1");
pub const COMMIT_MAGIC: u64 = u64::from_le_bytes(*b"LFSCOMIT");
pub const VERSION: u64 = 1;
pub const TABLE_SECTORS: u64 = 64;
pub const ENTRIES: usize = 256;
pub const AREA_LBA: [u64; 2] = [8, 72];
pub const DATA_LBA: u64 = 136;
pub const BLOCK_SECTORS: u64 = 8;
/// Kernel giữ bitmap khối trong RAM: tối đa 2^21 khối (8GB) — lớn hơn thì phần dư không được dùng
pub const MAX_BLOCKS: u64 = 1 << 21;
pub const F_USED: u64 = 1;
pub const F_DIR: u64 = 2;
pub const F_APP: u64 = 4;
pub const DEFAULT_SECTORS: u64 = 131072; // 64MB

/// Checksum 32-bit (FNV-1a trên từng nửa 32-bit của mỗi qword) — dễ viết trong Light mà không tràn số
pub fn cks(q: &[u64]) -> u64 {
    let mut h: u64 = 0x811C9DC5;
    for &x in q {
        h = ((h ^ (x & 0xffff_ffff)) * 0x0100_0193) & 0xffff_ffff;
        h = ((h ^ (x >> 32)) * 0x0100_0193) & 0xffff_ffff;
    }
    h
}

fn qwords(b: &[u8]) -> Vec<u64> {
    b.chunks(8).map(|c| u64::from_le_bytes(c.try_into().unwrap())).collect()
}
fn bytes(q: &[u64]) -> Vec<u8> {
    q.iter().flat_map(|x| x.to_le_bytes()).collect()
}
fn sectors_of(size: u64) -> u64 {
    size.div_ceil(SECTOR as u64)
}
fn blocks_of(size: u64) -> u64 {
    sectors_of(size).div_ceil(BLOCK_SECTORS)
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Entry {
    pub flags: u64,
    pub parent: u64,
    pub size: u64,
    pub start: u64,
    pub blocks: u64,
    pub cks: u64,
    pub generation: u64,
    pub name: Vec<u8>,
}

impl Entry {
    fn to_q(&self) -> [u64; 16] {
        let mut q = [0u64; 16];
        q[..7].copy_from_slice(&[self.flags, self.parent, self.size, self.start, self.blocks, self.cks, self.generation]);
        let mut nb = [0u8; 64];
        nb[..self.name.len().min(63)].copy_from_slice(&self.name[..self.name.len().min(63)]);
        for k in 0..8 {
            q[8 + k] = u64::from_le_bytes(nb[k * 8..k * 8 + 8].try_into().unwrap());
        }
        q
    }
    fn from_q(q: &[u64]) -> Entry {
        let nb = bytes(&q[8..16]);
        let n = nb.iter().position(|&b| b == 0).unwrap_or(64);
        Entry { flags: q[0], parent: q[1], size: q[2], start: q[3], blocks: q[4], cks: q[5], generation: q[6], name: nb[..n].to_vec() }
    }
    pub fn used(&self) -> bool {
        self.flags & F_USED != 0
    }
    pub fn is_dir(&self) -> bool {
        self.flags & F_DIR != 0
    }
}

pub fn valid_name(n: &[u8]) -> bool {
    !n.is_empty() && n.len() <= 63 && n.iter().all(|&b| (0x21..0x7f).contains(&b) && b != b'/') && n != b"." && n != b".."
}

// ---------------------------------------------------------------------------------------------- thiết bị
/// Ảnh đĩa: file thật (ảnh hoặc phân vùng) hoặc bộ nhớ (test). `log` ghi lại mọi lần ghi sector để mô phỏng mất điện.
#[allow(dead_code)]
pub enum Dev {
    File(File, u64),
    Mem(Vec<u8>),
}
impl Dev {
    pub fn open(path: &Path, write: bool) -> Result<Dev, String> {
        let mut f = OpenOptions::new().read(true).write(write).open(path).map_err(|e| format!("{}: {}", path.display(), e))?;
        let len = f.seek(SeekFrom::End(0)).map_err(|e| e.to_string())?;
        Ok(Dev::File(f, len / SECTOR as u64))
    }
    pub fn sectors(&self) -> u64 {
        match self {
            Dev::File(_, n) => *n,
            Dev::Mem(v) => (v.len() / SECTOR) as u64,
        }
    }
    pub fn read(&mut self, lba: u64, n: u64) -> Result<Vec<u8>, String> {
        if lba + n > self.sectors() {
            return Err(format!("đọc ngoài đĩa: LBA {} + {}", lba, n));
        }
        let (a, len) = (lba as usize * SECTOR, n as usize * SECTOR);
        match self {
            Dev::File(f, _) => {
                let mut b = vec![0u8; len];
                f.seek(SeekFrom::Start(a as u64)).map_err(|e| e.to_string())?;
                f.read_exact(&mut b).map_err(|e| e.to_string())?;
                Ok(b)
            }
            Dev::Mem(v) => Ok(v[a..a + len].to_vec()),
        }
    }
    pub fn write(&mut self, lba: u64, b: &[u8]) -> Result<(), String> {
        let n = b.len().div_ceil(SECTOR) as u64;
        if lba + n > self.sectors() {
            return Err(format!("ghi ngoài đĩa: LBA {} + {}", lba, n));
        }
        let mut buf = b.to_vec();
        buf.resize(n as usize * SECTOR, 0);
        match self {
            Dev::File(f, _) => {
                f.seek(SeekFrom::Start(lba * SECTOR as u64)).map_err(|e| e.to_string())?;
                f.write_all(&buf).map_err(|e| e.to_string())
            }
            Dev::Mem(v) => {
                let a = lba as usize * SECTOR;
                v[a..a + buf.len()].copy_from_slice(&buf);
                Ok(())
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------- hệ tệp
#[allow(dead_code)]
pub struct Fs {
    pub dev: Dev,
    pub total: u64,  // tổng sector theo header
    pub blocks: u64, // số khối dữ liệu dùng được
    pub generation: u64,
    pub area: u64,
    pub table: Vec<Entry>,
    /// Mọi lần ghi sector của thao tác gần nhất (lba, dữ liệu) — để test mất điện
    pub log: Vec<(u64, Vec<u8>)>,
    pub logging: bool,
}

fn header(total: u64) -> Vec<u64> {
    let mut h = vec![MAGIC, VERSION, total, TABLE_SECTORS, AREA_LBA[0], AREA_LBA[1], DATA_LBA, 0];
    h[7] = cks(&h[..7]);
    h
}
fn commit_rec(generation: u64, area: u64, tcks: u64) -> Vec<u64> {
    let mut c = vec![COMMIT_MAGIC, generation, area, tcks, 0, 0, 0, 0];
    c[7] = cks(&c[..7]);
    c
}
pub fn table_q(t: &[Entry]) -> Vec<u64> {
    t.iter().flat_map(|e| e.to_q()).collect()
}
pub fn data_blocks(total: u64) -> u64 {
    (total.saturating_sub(DATA_LBA) / BLOCK_SECTORS).min(MAX_BLOCKS)
}

/// Kết quả đọc một slot commit: Some((thế hệ, vùng, checksum bảng)) nếu bản ghi hợp lệ
fn read_commit(dev: &mut Dev, slot: u64) -> Result<Option<(u64, u64, u64)>, String> {
    let q = qwords(&dev.read(1 + slot, 1)?);
    if q[0] != COMMIT_MAGIC || q[7] != cks(&q[..7]) || q[2] > 1 {
        return Ok(None);
    }
    Ok(Some((q[1], q[2], q[3])))
}

#[allow(dead_code)]
impl Fs {
    /// Tạo hệ tệp rỗng (chỉ có thư mục gốc) trên `dev`, dùng `total` sector đầu
    pub fn format(mut dev: Dev, total: u64) -> Result<Fs, String> {
        if total < DATA_LBA + BLOCK_SECTORS || total > dev.sectors() {
            return Err(format!("kích thước hệ tệp {} sector không hợp lệ (thiết bị {} sector)", total, dev.sectors()));
        }
        dev.write(0, &bytes(&header(total)))?;
        let mut table = vec![Entry::default(); ENTRIES];
        table[0] = Entry { flags: F_USED | F_DIR, ..Default::default() };
        let tq = table_q(&table);
        dev.write(AREA_LBA[0], &bytes(&tq))?;
        dev.write(AREA_LBA[1], &vec![0u8; TABLE_SECTORS as usize * SECTOR])?;
        dev.write(1, &bytes(&commit_rec(1, 0, cks(&tq))))?;
        dev.write(2, &[0u8; SECTOR])?;
        Ok(Fs { dev, total, blocks: data_blocks(total), generation: 1, area: 0, table, log: vec![], logging: false })
    }

    /// Gắn hệ tệp: header hợp lệ + bản ghi commit hợp lệ mới nhất có bảng khớp checksum (không được thì slot kia)
    pub fn mount(mut dev: Dev) -> Result<Fs, String> {
        let h = qwords(&dev.read(0, 1)?);
        if h[0] != MAGIC {
            return Err("không phải LightFS (thiếu magic LIGHTFS1)".into());
        }
        if h[7] != cks(&h[..7]) || h[1] != VERSION || h[3] != TABLE_SECTORS || h[4] != AREA_LBA[0] || h[5] != AREA_LBA[1] || h[6] != DATA_LBA {
            return Err("header LightFS hỏng hoặc khác phiên bản".into());
        }
        let total = h[2];
        if total > dev.sectors() || total < DATA_LBA {
            return Err(format!("header ghi {} sector nhưng thiết bị chỉ có {}", total, dev.sectors()));
        }
        let mut cands: Vec<(u64, u64, u64)> = (0..2).filter_map(|s| read_commit(&mut dev, s).ok().flatten()).collect();
        cands.sort_by(|a, b| b.0.cmp(&a.0));
        for (generation, area, tc) in cands {
            let tq = qwords(&dev.read(AREA_LBA[area as usize], TABLE_SECTORS)?);
            if cks(&tq) == tc {
                let table = tq.chunks(16).map(Entry::from_q).collect();
                return Ok(Fs { dev, total, blocks: data_blocks(total), generation, area, table, log: vec![], logging: false });
            }
        }
        Err("không có bản ghi commit nào hợp lệ (cả hai slot hỏng hoặc bảng sai checksum)".into())
    }

    fn wr(&mut self, lba: u64, b: &[u8]) -> Result<(), String> {
        if self.logging {
            let mut p = b.to_vec();
            p.resize(b.len().div_ceil(SECTOR) * SECTOR, 0);
            for (k, s) in p.chunks(SECTOR).enumerate() {
                self.log.push((lba + k as u64, s.to_vec()));
            }
        }
        self.dev.write(lba, b)
    }

    /// Bitmap khối đang dùng theo bảng hiện tại
    pub fn used_blocks(&self) -> Vec<bool> {
        let mut m = vec![false; self.blocks as usize];
        for e in self.table.iter().filter(|e| e.used() && !e.is_dir()) {
            for b in e.start..(e.start + e.blocks).min(self.blocks) {
                m[b as usize] = true;
            }
        }
        m
    }
    /// Khối trống liên tục đầu tiên đủ `n` khối (first-fit)
    fn alloc(&self, n: u64) -> Option<u64> {
        if n == 0 {
            return Some(0);
        }
        let m = self.used_blocks();
        let mut run = 0;
        for (b, &u) in m.iter().enumerate() {
            run = if u { 0 } else { run + 1 };
            if run == n {
                return Some(b as u64 + 1 - n);
            }
        }
        None
    }

    fn commit(&mut self) -> Result<(), String> {
        let tq = table_q(&self.table);
        let na = 1 - self.area;
        self.wr(AREA_LBA[na as usize], &bytes(&tq))?;
        let ng = self.generation + 1;
        self.wr(1 + ng % 2, &bytes(&commit_rec(ng, na, cks(&tq))))?;
        self.generation = ng;
        self.area = na;
        Ok(())
    }

    pub fn find(&self, parent: u64, name: &[u8]) -> Option<u64> {
        (1..ENTRIES).find(|&i| self.table[i].used() && self.table[i].parent == parent && self.table[i].name == name).map(|i| i as u64)
    }
    /// Đường dẫn dạng "a/b/c" -> chỉ số mục
    pub fn lookup(&self, path: &str) -> Option<u64> {
        let mut cur = 0;
        for seg in path.split('/').filter(|s| !s.is_empty()) {
            cur = self.find(cur, seg.as_bytes())?;
        }
        Some(cur)
    }
    pub fn path_of(&self, mut i: u64) -> String {
        let mut parts = vec![];
        let mut guard = 0;
        while i != 0 && guard < ENTRIES {
            parts.push(String::from_utf8_lossy(&self.table[i as usize].name).to_string());
            i = self.table[i as usize].parent;
            guard += 1;
        }
        parts.reverse();
        parts.join("/")
    }

    pub fn create(&mut self, parent: u64, name: &[u8], flags: u64) -> Result<u64, String> {
        let p = self.table.get(parent as usize).ok_or("thư mục cha không tồn tại")?;
        if !p.used() || !p.is_dir() {
            return Err("cha không phải thư mục".into());
        }
        if !valid_name(name) {
            return Err(format!("tên không hợp lệ: {:?}", String::from_utf8_lossy(name)));
        }
        if self.find(parent, name).is_some() {
            return Err(format!("đã tồn tại: {}", String::from_utf8_lossy(name)));
        }
        let id = (1..ENTRIES).find(|&i| !self.table[i].used()).ok_or("bảng đầy (256 mục)")?;
        self.table[id] = Entry { flags: F_USED | (flags & (F_DIR | F_APP)), parent, cks: cks(&[]), generation: self.generation + 1, name: name.to_vec(), ..Default::default() };
        self.commit()?;
        Ok(id as u64)
    }

    /// Ghi đè toàn bộ nội dung file (copy-on-write)
    pub fn write_file(&mut self, id: u64, data: &[u8]) -> Result<(), String> {
        let e = self.table.get(id as usize).cloned().ok_or("mục không tồn tại")?;
        if !e.used() || e.is_dir() || id == 0 {
            return Err("không phải file".into());
        }
        let n = blocks_of(data.len() as u64);
        let start = self.alloc(n).ok_or("hết chỗ trống liên tục")?;
        let mut padded = data.to_vec();
        padded.resize(sectors_of(data.len() as u64) as usize * SECTOR, 0);
        if !padded.is_empty() {
            self.wr(DATA_LBA + start * BLOCK_SECTORS, &padded)?;
        }
        let t = &mut self.table[id as usize];
        t.size = data.len() as u64;
        t.start = start;
        t.blocks = n;
        t.cks = cks(&qwords(&padded));
        t.generation = self.generation + 1;
        self.commit()
    }

    pub fn delete(&mut self, id: u64) -> Result<(), String> {
        if id == 0 || id as usize >= ENTRIES || !self.table[id as usize].used() {
            return Err("không xóa được mục này".into());
        }
        if self.table.iter().any(|e| e.used() && e.parent == id) {
            return Err("thư mục chưa rỗng".into());
        }
        self.table[id as usize] = Entry::default();
        self.commit()
    }

    pub fn read_file(&mut self, id: u64) -> Result<Vec<u8>, String> {
        let e = self.table[id as usize].clone();
        let sec = sectors_of(e.size);
        let raw = if sec > 0 { self.dev.read(DATA_LBA + e.start * BLOCK_SECTORS, sec)? } else { vec![] };
        if cks(&qwords(&raw)) != e.cks {
            return Err(format!("{}: sai checksum dữ liệu", self.path_of(id)));
        }
        Ok(raw[..e.size as usize].to_vec())
    }

    /// Tạo các thư mục còn thiếu theo đường dẫn, trả chỉ số thư mục cuối
    pub fn mkdirs(&mut self, path: &str) -> Result<u64, String> {
        let mut cur = 0;
        for seg in path.split('/').filter(|s| !s.is_empty()) {
            cur = match self.find(cur, seg.as_bytes()) {
                Some(i) => i,
                None => self.create(cur, seg.as_bytes(), F_DIR)?,
            };
        }
        Ok(cur)
    }
}

// ---------------------------------------------------------------------------------------------- fsck
#[derive(Default, Debug)]
pub struct Report {
    pub errors: Vec<String>,
    pub notes: Vec<String>,
    pub files: usize,
    pub dirs: usize,
    pub used_blocks: u64,
}

pub fn fsck(dev: Dev) -> Report {
    let mut r = Report::default();
    let mut dev = dev;
    let mut slots = vec![];
    for s in 0..2 {
        match read_commit(&mut dev, s) {
            Ok(Some((g, a, _))) => slots.push(format!("slot {}: thế hệ {} vùng {}", s, g, a)),
            _ => slots.push(format!("slot {}: trống/hỏng", s)),
        }
    }
    let mut fs = match Fs::mount(dev) {
        Ok(f) => f,
        Err(e) => {
            r.errors.push(e);
            return r;
        }
    };
    r.notes.extend(slots);
    r.notes.push(format!("dùng thế hệ {} (vùng {}), {} khối dữ liệu", fs.generation, fs.area, fs.blocks));
    let t = fs.table.clone();
    if t[0].flags != F_USED | F_DIR {
        r.errors.push("mục 0 không phải thư mục gốc".into());
    }
    let mut owner: Vec<Option<usize>> = vec![None; fs.blocks as usize];
    let mut names = HashSet::new();
    for (i, e) in t.iter().enumerate().skip(1) {
        if !e.used() {
            if e.flags != 0 {
                r.errors.push(format!("mục {} chưa dùng nhưng cờ = {:#x}", i, e.flags));
            }
            continue;
        }
        let path = fs.path_of(i as u64);
        if e.flags & !(F_USED | F_DIR | F_APP) != 0 {
            r.errors.push(format!("{}: cờ lạ {:#x}", path, e.flags));
        }
        if !valid_name(&e.name) {
            r.errors.push(format!("mục {}: tên không hợp lệ {:?}", i, String::from_utf8_lossy(&e.name)));
        }
        let p = e.parent as usize;
        if p >= ENTRIES || !t[p].used() || !t[p].is_dir() {
            r.errors.push(format!("{}: thư mục cha {} không hợp lệ", path, p));
        }
        if !names.insert((e.parent, e.name.clone())) {
            r.errors.push(format!("{}: trùng tên trong cùng thư mục", path));
        }
        // Chu trình cha-con
        let (mut cur, mut steps) = (i, 0);
        while cur != 0 && steps <= ENTRIES {
            cur = t[cur].parent as usize % ENTRIES;
            steps += 1;
        }
        if steps > ENTRIES {
            r.errors.push(format!("mục {}: chu trình thư mục cha", i));
        }
        if e.is_dir() {
            r.dirs += 1;
            if e.size != 0 || e.blocks != 0 {
                r.errors.push(format!("{}: thư mục có dữ liệu", path));
            }
            continue;
        }
        r.files += 1;
        if e.blocks != blocks_of(e.size) {
            r.errors.push(format!("{}: số khối {} không khớp kích thước {}", path, e.blocks, e.size));
        }
        if e.start + e.blocks > fs.blocks {
            r.errors.push(format!("{}: extent {}+{} vượt vùng dữ liệu ({} khối)", path, e.start, e.blocks, fs.blocks));
            continue;
        }
        for b in e.start..e.start + e.blocks {
            if let Some(o) = owner[b as usize] {
                r.errors.push(format!("{}: khối {} trùng với {}", path, b, fs.path_of(o as u64)));
                break;
            }
            owner[b as usize] = Some(i);
        }
        r.used_blocks += e.blocks;
        if let Err(err) = fs.read_file(i as u64) {
            r.errors.push(err);
        }
    }
    r
}

// ---------------------------------------------------------------------------------------------- pack / sync
/// Đóng gói cây `storage_root` thành ảnh LightFS `disk_path` (`total` sector, file thưa)
pub fn pack(storage_root: &Path, disk_path: &Path, total: u64) -> Result<Fs, String> {
    let f = File::create(disk_path).map_err(|e| format!("{}: {}", disk_path.display(), e))?;
    f.set_len(total * SECTOR as u64).map_err(|e| e.to_string())?;
    drop(f);
    let mut fs = Fs::format(Dev::open(disk_path, true)?, total)?;
    let mut items: BTreeMap<String, Option<std::path::PathBuf>> = BTreeMap::new();
    fn walk(dir: &Path, rel: &str, out: &mut BTreeMap<String, Option<std::path::PathBuf>>) -> Result<(), String> {
        let mut ents: Vec<_> = fs::read_dir(dir).map_err(|e| e.to_string())?.filter_map(|e| e.ok()).collect();
        ents.sort_by_key(|e| e.file_name());
        for e in ents {
            let name = e.file_name().to_string_lossy().to_string();
            let r = if rel.is_empty() { name.clone() } else { format!("{}/{}", rel, name) };
            let p = e.path();
            if p.is_dir() {
                out.insert(r.clone(), None);
                walk(&p, &r, out)?;
            } else if p.is_file() {
                out.insert(r, Some(p));
            }
        }
        Ok(())
    }
    walk(storage_root, "", &mut items)?;
    for (rel, src) in &items {
        let (dir, name) = rel.rsplit_once('/').unwrap_or(("", rel));
        let parent = fs.mkdirs(dir)?;
        match src {
            None => {
                fs.mkdirs(rel)?;
            }
            Some(p) => {
                let data = fs::read(p).map_err(|e| format!("{}: {}", p.display(), e))?;
                let app = if dir == "apps" && name.ends_with(".elf") { F_APP } else { 0 };
                let id = fs.create(parent, name.as_bytes(), app)?;
                fs.write_file(id, &data)?;
            }
        }
    }
    Ok(fs)
}

/// Chép mọi file trên ảnh về cây `storage_root` (ghi đè). Trả (số file đã ghi, file hỏng checksum bị bỏ qua)
pub fn sync(dev: Dev, storage_root: &Path) -> Result<(usize, Vec<String>), String> {
    let mut fs = Fs::mount(dev)?;
    let (mut n, mut bad) = (0, vec![]);
    for i in 1..ENTRIES as u64 {
        let e = fs.table[i as usize].clone();
        if !e.used() {
            continue;
        }
        let dest = storage_root.join(fs.path_of(i));
        if e.is_dir() {
            fs::create_dir_all(&dest).map_err(|er| er.to_string())?;
            continue;
        }
        match fs.read_file(i) {
            Ok(data) => {
                if let Some(p) = dest.parent() {
                    fs::create_dir_all(p).map_err(|er| er.to_string())?;
                }
                fs::write(&dest, data).map_err(|er| er.to_string())?;
                n += 1;
            }
            Err(er) => bad.push(er),
        }
    }
    Ok((n, bad))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mem_fs(total: u64) -> Fs {
        Fs::format(Dev::Mem(vec![0u8; total as usize * SECTOR]), total).unwrap()
    }
    fn snapshot(fs: &Fs) -> Vec<u8> {
        match &fs.dev {
            Dev::Mem(v) => v.clone(),
            _ => unreachable!(),
        }
    }
    fn ok(dev: Dev) -> Report {
        let r = fsck(dev);
        assert!(r.errors.is_empty(), "fsck báo lỗi: {:?}", r.errors);
        r
    }

    #[test]
    fn create_write_read_delete() {
        let mut fs = mem_fs(4096);
        let d = fs.mkdirs("data/sub").unwrap();
        let f = fs.create(d, b"a.txt", 0).unwrap();
        fs.write_file(f, b"hello").unwrap();
        fs.write_file(f, &vec![7u8; 10000]).unwrap();
        assert_eq!(fs.read_file(f).unwrap(), vec![7u8; 10000]);
        assert!(fs.create(d, b"a.txt", 0).is_err());
        assert!(fs.create(d, b"x/y", 0).is_err());
        assert!(fs.delete(d).is_err(), "thư mục chưa rỗng phải bị từ chối");
        let r = ok(Dev::Mem(snapshot(&fs)));
        assert_eq!((r.files, r.dirs), (1, 2));
        let mut fs = Fs::mount(Dev::Mem(snapshot(&fs))).unwrap();
        assert_eq!(fs.lookup("data/sub/a.txt"), Some(f));
        fs.delete(f).unwrap();
        fs.delete(d).unwrap();
        assert_eq!(ok(Dev::Mem(snapshot(&fs))).files, 0);
    }

    #[test]
    fn full_disk_and_table() {
        let mut fs = mem_fs(DATA_LBA + 8 * 10); // 10 khối
        let f = fs.create(0, b"big", 0).unwrap();
        assert!(fs.write_file(f, &vec![1u8; 4096 * 11]).is_err());
        fs.write_file(f, &vec![1u8; 4096 * 6]).unwrap();
        // 6 khối đang dùng, còn 4: ghi lại 5 khối phải thất bại (copy-on-write cần khối mới) và giữ nguyên dữ liệu cũ
        assert!(fs.write_file(f, &vec![2u8; 4096 * 5]).is_err());
        assert_eq!(fs.read_file(f).unwrap(), vec![1u8; 4096 * 6]);
        fs.write_file(f, &vec![3u8; 4096 * 4]).unwrap();
        ok(Dev::Mem(snapshot(&fs)));
        for k in 0..254 {
            fs.create(0, format!("f{}", k).as_bytes(), 0).unwrap();
        }
        assert!(fs.create(0, b"tran", 0).is_err(), "bảng 256 mục phải đầy");
        ok(Dev::Mem(snapshot(&fs)));
    }

    /// Mất điện ở MỌI điểm giữa các lần ghi sector của một thao tác (kể cả ghi dở một sector):
    /// sau đó hệ tệp phải gắn được, fsck sạch, và nội dung là trạng thái cũ HOẶC mới — không bao giờ lẫn lộn.
    #[test]
    fn power_loss_every_point() {
        let mut base = mem_fs(2048);
        let f = base.create(0, b"note.txt", 0).unwrap();
        base.write_file(f, b"phien ban cu").unwrap();
        let before = snapshot(&base);
        let new_data = vec![b'N'; 3000];
        base.logging = true;
        base.write_file(f, &new_data).unwrap();
        let log = base.log.clone();
        assert!(log.len() >= 3);
        for cut in 0..=log.len() {
            for torn in [false, true] {
                if torn && cut == log.len() {
                    continue;
                }
                let mut img = before.clone();
                for (lba, s) in &log[..cut] {
                    img[*lba as usize * SECTOR..(*lba as usize + 1) * SECTOR].copy_from_slice(s);
                }
                if torn {
                    // sector kế tiếp chỉ ghi được nửa đầu
                    let (lba, s) = &log[cut];
                    img[*lba as usize * SECTOR..*lba as usize * SECTOR + 256].copy_from_slice(&s[..256]);
                }
                ok(Dev::Mem(img.clone()));
                let mut fs = Fs::mount(Dev::Mem(img)).unwrap();
                let got = fs.read_file(f).unwrap();
                assert!(got == b"phien ban cu" || got == new_data, "cắt tại {}: nội dung lẫn lộn", cut);
                if cut == log.len() {
                    assert_eq!(got, new_data);
                }
            }
        }
    }

    #[test]
    fn corruption_detected() {
        let mut fs = mem_fs(2048);
        let f = fs.create(0, b"x", 0).unwrap();
        fs.write_file(f, b"du lieu quan trong").unwrap();
        let img = snapshot(&fs);
        // Hỏng dữ liệu file -> fsck báo sai checksum
        let mut a = img.clone();
        let lba = (DATA_LBA + fs.table[f as usize].start * BLOCK_SECTORS) as usize;
        a[lba * SECTOR] ^= 1;
        assert!(fsck(Dev::Mem(a)).errors.iter().any(|e| e.contains("checksum")));
        // Hỏng bảng hiện hành -> gắn bằng thế hệ trước (slot kia) và vẫn sạch
        let mut b = img.clone();
        let cur = AREA_LBA[fs.area as usize] as usize;
        b[cur * SECTOR + 100] ^= 0xff;
        let fb = Fs::mount(Dev::Mem(b.clone())).unwrap();
        assert_eq!(fb.generation, fs.generation - 1);
        ok(Dev::Mem(b));
        // Hỏng cả hai slot commit -> không gắn được
        let mut c = img.clone();
        c[SECTOR + 8] ^= 1;
        c[2 * SECTOR + 8] ^= 1;
        assert!(Fs::mount(Dev::Mem(c)).is_err());
        // Không phải LightFS
        assert!(Fs::mount(Dev::Mem(vec![0u8; 2048 * SECTOR])).is_err());
    }
}
