// File: src/vfs.rs (Virtual Flat Filesystem for Light OS)
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};

pub const SECTOR_SIZE: usize = 512;
pub const VFS_MAGIC: &[u8; 8] = b"LIGHTVFS";

pub const FLAG_APP: u32 = 0x01;
pub const FLAG_DATA: u32 = 0x02;
pub const FLAG_MODIFIED: u32 = 0x04;
pub const FLAG_DELETED: u32 = 0x80;

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct Superblock {
    pub magic: [u8; 8],
    pub font_lba: u64,
    pub dir_start_lba: u64,
    pub dir_sector_count: u64,
    pub pool_start_lba: u64,
    pub pool_sector_count: u64,
    pub next_free_lba: u64,
    pub total_files: u64,
}

impl Superblock {
    pub fn to_bytes(&self) -> [u8; SECTOR_SIZE] {
        let mut buf = [0u8; SECTOR_SIZE];
        buf[0..8].copy_from_slice(&self.magic);
        buf[8..16].copy_from_slice(&self.font_lba.to_le_bytes());
        buf[16..24].copy_from_slice(&self.dir_start_lba.to_le_bytes());
        buf[24..32].copy_from_slice(&self.dir_sector_count.to_le_bytes());
        buf[32..40].copy_from_slice(&self.pool_start_lba.to_le_bytes());
        buf[40..48].copy_from_slice(&self.pool_sector_count.to_le_bytes());
        buf[48..56].copy_from_slice(&self.next_free_lba.to_le_bytes());
        buf[56..64].copy_from_slice(&self.total_files.to_le_bytes());
        buf
    }

    pub fn from_bytes(buf: &[u8]) -> Result<Self, String> {
        if buf.len() < SECTOR_SIZE {
            return Err("Buffer nhỏ hơn 1 sector".to_string());
        }
        if &buf[0..8] != VFS_MAGIC {
            return Err("Sai Superblock Magic (Không phải LIGHTVFS)".to_string());
        }
        let read_u64 = |start: usize| -> u64 {
            let mut b = [0u8; 8];
            b.copy_from_slice(&buf[start..start + 8]);
            u64::from_le_bytes(b)
        };
        Ok(Superblock {
            magic: *VFS_MAGIC,
            font_lba: read_u64(8),
            dir_start_lba: read_u64(16),
            dir_sector_count: read_u64(24),
            pool_start_lba: read_u64(32),
            pool_sector_count: read_u64(40),
            next_free_lba: read_u64(48),
            total_files: read_u64(56),
        })
    }
}

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct VfsEntry {
    pub short_name: [u8; 8], // 8 ký tự ngắn (ví dụ "NOTE.TXT")
    pub path_offset: u32,    // Offset trong Path String Pool
    pub path_len: u32,       // Độ dài relative path
    pub start_sec: u64,      // LBA sector bắt đầu
    pub file_size: u64,      // Kích thước byte thực tế (64-bit đầy đủ)
    pub flags: u32,          // Cờ trạng thái
}

impl VfsEntry {
    pub const SIZE: usize = 32;

    pub fn to_bytes(&self) -> [u8; Self::SIZE] {
        let mut buf = [0u8; Self::SIZE];
        buf[0..8].copy_from_slice(&self.short_name);
        buf[8..12].copy_from_slice(&self.path_offset.to_le_bytes());
        buf[12..16].copy_from_slice(&self.path_len.to_le_bytes());
        let sec_and_flags = (self.start_sec & 0xffff_ffff) | ((self.flags as u64) << 32);
        buf[16..24].copy_from_slice(&sec_and_flags.to_le_bytes());
        buf[24..32].copy_from_slice(&self.file_size.to_le_bytes());
        buf
    }

    pub fn from_bytes(buf: &[u8]) -> Self {
        let mut short_name = [0u8; 8];
        short_name.copy_from_slice(&buf[0..8]);
        let read_u32 = |s: usize| {
            let mut b = [0u8; 4];
            b.copy_from_slice(&buf[s..s + 4]);
            u32::from_le_bytes(b)
        };
        let read_u64 = |s: usize| {
            let mut b = [0u8; 8];
            b.copy_from_slice(&buf[s..s + 8]);
            u64::from_le_bytes(b)
        };
        let sec_and_flags = read_u64(16);
        let start_sec = sec_and_flags & 0xffff_ffff;
        let flags = (sec_and_flags >> 32) as u32;
        let file_size = read_u64(24);
        Self {
            short_name,
            path_offset: read_u32(8),
            path_len: read_u32(12),
            start_sec,
            file_size,
            flags,
        }
    }
}

fn to_short_name(name: &str) -> [u8; 8] {
    let mut out = [b' '; 8];
    let upper = name.to_ascii_uppercase();
    let bytes = upper.as_bytes();
    let len = bytes.len().min(8);
    out[..len].copy_from_slice(&bytes[..len]);
    out
}

fn collect_files_recursive(
    dir: &Path,
    base: &Path,
    list: &mut Vec<(PathBuf, String)>,
) -> Result<(), String> {
    if !dir.exists() {
        return Ok(());
    }
    for entry in fs::read_dir(dir).map_err(|e| e.to_string())? {
        let entry = entry.map_err(|e| e.to_string())?;
        let p = entry.path();
        if p.is_dir() {
            collect_files_recursive(&p, base, list)?;
        } else if p.is_file() {
            let rel = p
                .strip_prefix(base)
                .map_err(|e| e.to_string())?
                .to_string_lossy()
                .to_string();
            list.push((p, rel));
        }
    }
    Ok(())
}

pub fn pack_storage_to_disk(storage_root: &Path, disk_path: &Path) -> Result<Superblock, String> {
    let mut file_list = Vec::new();
    let mut apps_list = Vec::new();
    let mut data_list = Vec::new();

    collect_files_recursive(&storage_root.join("apps"), storage_root, &mut apps_list)?;
    collect_files_recursive(&storage_root.join("data"), storage_root, &mut data_list)?;

    apps_list.sort_by(|a, b| a.1.cmp(&b.1));
    // Sắp xếp các file nhỏ (< 1GB) lên trước để LBA của các file runtime luôn nằm ở đầu đĩa (< 65536 sectors)
    data_list.sort_by(|a, b| {
        let size_a = fs::metadata(&a.0).map(|m| m.len()).unwrap_or(0);
        let size_b = fs::metadata(&b.0).map(|m| m.len()).unwrap_or(0);
        size_a.cmp(&size_b).then_with(|| a.1.cmp(&b.1))
    });
    file_list.extend(apps_list);
    file_list.extend(data_list);

    let mut string_pool = Vec::new();
    let mut entries = Vec::new();

    // Sector 0: Superblock (1 sector)
    let font_lba = 0u64;

    // Directory Table bắt đầu ngay từ Sector 1 (tối thiểu 16 sectors = 256 files)
    let dir_start_lba = 1u64;
    let min_dir_sectors = 16u64;
    let needed_dir_sectors =
        ((file_list.len() * VfsEntry::SIZE + SECTOR_SIZE - 1) / SECTOR_SIZE) as u64;
    let dir_sector_count = needed_dir_sectors.max(min_dir_sectors);

    // Dự trù String Pool: tối thiểu 16 sectors (8 KB chuỗi path)
    let pool_start_lba = dir_start_lba + dir_sector_count;
    let min_pool_sectors = 16u64;

    // Data payload bắt đầu sau String Pool
    let mut cur_data_lba = pool_start_lba + min_pool_sectors;

    let mut file_data_paths: Vec<(u64, PathBuf)> = Vec::new();

    for (abs_path, rel_path) in &file_list {
        let metadata = fs::metadata(abs_path)
            .map_err(|e| format!("Không thể lấy thông tin {:?}: {}", abs_path, e))?;
        let size = metadata.len();

        let path_offset = string_pool.len() as u32;
        let path_bytes = rel_path.as_bytes();
        let path_len = path_bytes.len() as u32;
        string_pool.extend_from_slice(path_bytes);
        string_pool.push(0); // null terminator

        let filename = Path::new(rel_path)
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("UNKNOWN");
        let short_name = to_short_name(filename);

        let sector_count = ((size as usize + SECTOR_SIZE - 1) / SECTOR_SIZE).max(1) as u64;
        let start_sec = cur_data_lba;
        cur_data_lba += sector_count;

        let flags = if rel_path.starts_with("apps/") {
            FLAG_APP
        } else {
            FLAG_DATA
        };

        entries.push(VfsEntry {
            short_name,
            path_offset,
            path_len,
            start_sec,
            file_size: size,
            flags,
        });

        file_data_paths.push((start_sec, abs_path.clone()));
    }

    let needed_pool_sectors = ((string_pool.len() + SECTOR_SIZE - 1) / SECTOR_SIZE) as u64;
    let pool_sector_count = needed_pool_sectors.max(min_pool_sectors);

    // Nếu pool thực tế lớn hơn min_pool_sectors thì offset data cần dịch
    let diff = pool_sector_count - min_pool_sectors;
    if diff > 0 {
        for entry in &mut entries {
            entry.start_sec += diff;
        }
        for (sec, _) in &mut file_data_paths {
            *sec += diff;
        }
        cur_data_lba += diff;
    }

    let sb = Superblock {
        magic: *VFS_MAGIC,
        font_lba,
        dir_start_lba,
        dir_sector_count,
        pool_start_lba,
        pool_sector_count,
        next_free_lba: cur_data_lba,
        total_files: entries.len() as u64,
    };

    // Tạo file đĩa (làm tròn lên bội số sector)
    let total_disk_sectors = cur_data_lba.max(128); // Tối thiểu 64 KB
    let mut disk_file =
        File::create(disk_path).map_err(|e| format!("Lỗi tạo {:?}: {}", disk_path, e))?;
    disk_file
        .set_len(total_disk_sectors * SECTOR_SIZE as u64)
        .map_err(|e| format!("Lỗi đặt kích thước đĩa: {}", e))?;

    // 1. Ghi Superblock
    disk_file
        .seek(SeekFrom::Start(0))
        .map_err(|e| e.to_string())?;
    disk_file
        .write_all(&sb.to_bytes())
        .map_err(|e| e.to_string())?;

    // 2. Ghi Directory Table tại Sector 1
    disk_file
        .seek(SeekFrom::Start(dir_start_lba * SECTOR_SIZE as u64))
        .map_err(|e| e.to_string())?;
    for entry in &entries {
        disk_file
            .write_all(&entry.to_bytes())
            .map_err(|e| e.to_string())?;
    }

    // 4. Ghi String Pool
    disk_file
        .seek(SeekFrom::Start(pool_start_lba * SECTOR_SIZE as u64))
        .map_err(|e| e.to_string())?;
    disk_file
        .write_all(&string_pool)
        .map_err(|e| e.to_string())?;

    // 5. Ghi các file data (truyền dòng trực tiếp tiết kiệm RAM tối đa, buffer 4MB siêu tốc trên NVMe)
    let mut stream_buf = vec![0u8; 4 * 1024 * 1024];
    for (start_sec, abs_path) in file_data_paths {
        disk_file
            .seek(SeekFrom::Start(start_sec * SECTOR_SIZE as u64))
            .map_err(|e| e.to_string())?;
        let mut src_file = File::open(&abs_path)
            .map_err(|e| format!("Không thể mở {:?}: {}", abs_path, e))?;
        loop {
            let n = src_file
                .read(&mut stream_buf)
                .map_err(|e| format!("Lỗi đọc {:?}: {}", abs_path, e))?;
            if n == 0 {
                break;
            }
            disk_file
                .write_all(&stream_buf[..n])
                .map_err(|e| format!("Lỗi ghi {:?}: {}", abs_path, e))?;
        }
    }

    disk_file.flush().map_err(|e| e.to_string())?;

    println!(
        "  ✓ VFS Packed: {} files (dir: {} secs, pool: {} secs, next_free_lba: {})",
        sb.total_files, sb.dir_sector_count, sb.pool_sector_count, sb.next_free_lba
    );

    Ok(sb)
}

/// Đồng bộ ngược từ `disk.img` về cây thư mục Linux `storage/`
pub fn sync_disk_to_storage(disk_path: &Path, storage_root: &Path) -> Result<usize, String> {
    let mut disk_file = OpenOptions::new()
        .read(true)
        .write(true)
        .open(disk_path)
        .map_err(|e| format!("Không thể mở {:?}: {}", disk_path, e))?;

    let mut sb_buf = [0u8; SECTOR_SIZE];
    disk_file
        .read_exact(&mut sb_buf)
        .map_err(|e| e.to_string())?;
    let sb = Superblock::from_bytes(&sb_buf)?;

    let mut dir_buf = vec![0u8; (sb.dir_sector_count as usize) * SECTOR_SIZE];
    disk_file
        .seek(SeekFrom::Start(sb.dir_start_lba * SECTOR_SIZE as u64))
        .map_err(|e| e.to_string())?;
    disk_file
        .read_exact(&mut dir_buf)
        .map_err(|e| e.to_string())?;

    let mut pool_buf = vec![0u8; (sb.pool_sector_count as usize) * SECTOR_SIZE];
    disk_file
        .seek(SeekFrom::Start(sb.pool_start_lba * SECTOR_SIZE as u64))
        .map_err(|e| e.to_string())?;
    disk_file
        .read_exact(&mut pool_buf)
        .map_err(|e| e.to_string())?;

    let mut count = 0;
    for i in 0..(sb.total_files as usize) {
        let entry_bytes = &dir_buf[i * VfsEntry::SIZE..(i + 1) * VfsEntry::SIZE];
        let entry = VfsEntry::from_bytes(entry_bytes);
        if entry.flags & FLAG_DELETED != 0 {
            continue;
        }
        let poff = entry.path_offset as usize;
        let plen = entry.path_len as usize;
        if poff + plen > pool_buf.len() {
            continue;
        }
        let rel_path = String::from_utf8_lossy(&pool_buf[poff..poff + plen]).to_string();
        let mut file_buf = vec![0u8; SECTOR_SIZE];
        disk_file
            .seek(SeekFrom::Start(entry.start_sec * SECTOR_SIZE as u64))
            .map_err(|e| e.to_string())?;
        disk_file
            .read_exact(&mut file_buf)
            .map_err(|e| e.to_string())?;
        let actual_len = file_buf
            .iter()
            .position(|&b| b == 0)
            .unwrap_or(entry.file_size as usize);
        let file_buf = &file_buf[..actual_len];

        let dest = storage_root.join(&rel_path);
        if let Some(parent) = dest.parent() {
            fs::create_dir_all(parent).map_err(|e| e.to_string())?;
        }
        fs::write(&dest, &file_buf).map_err(|e| e.to_string())?;
        count += 1;
    }
    Ok(count)
}
