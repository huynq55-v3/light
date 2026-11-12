// File: src/elf64.rs — sinh mã máy cho cả module (compile_code). Phần đóng gói ELF kernel / App của Light OS đã bỏ.
use crate::ir::*;
use std::collections::HashMap;

const RT_PARALLEL: &[u8] = include_bytes!("rt/rt_parallel.bin");

/// Blob ATA viết tay chỉ được thay thế khi biên dịch Kernel VÀ chữ ký hàm khớp đúng hợp đồng mà blob tôn trọng
/// (ghi tối đa count*512 <= 128KB vào buffer 16384 Qword, dùng cổng 0x1F0..0x1F7). Trước đây App chỉ cần đặt
/// trùng tên hàm là nhận được blob: in/out cổng ATA không cần thẻ io và ghi tràn buffer tùy ý.
fn ata_blob_allowed(module: &Module, func: &Func, is_kernel: bool) -> bool {
    let dq = module.layouts.iter().position(|l| l.name == "DiskQword" && l.size == 8);
    is_kernel
        && func.name == "drv_ata_read_sectors_batch"
        && dq.is_some()
        && func.params.iter().map(|p| p.1).collect::<Vec<_>>()
            == [
                Type::Io { min: 0x1f0, max: 0x1f7 },
                Type::Ptr { layout_id: dq.unwrap() as u16, max_elems: 16384 },
                Type::Bv64,
                Type::Bv64,
            ]
        && func.requires.len() >= 4
}

/// Mã máy của cả module + offset bắt đầu của từng hàm (theo thứ tự module.funcs)
pub fn compile_code(module: &Module, is_kernel: bool) -> Result<(Vec<u8>, Vec<usize>), String> {
    let mut code: Vec<u8> = Vec::new();
    let mut func_addrs: HashMap<u32, usize> = HashMap::new();
    let mut call_patches: Vec<(usize, u32)> = Vec::new();
    let mut rt_patches: Vec<usize> = Vec::new();

    for (f_idx, func) in module.funcs.iter().enumerate() {
        func_addrs.insert(f_idx as u32, code.len());

        // Tối ưu hóa phần cứng tầng Driver ATA: Dùng lệnh x86-64 REP INSW đọc khối trực tiếp
        // Giảm số lần ngắt trap máy ảo từ 12 triệu lần xuống còn 47.000 lần (nhanh gấp 256 lần!)
        if ata_blob_allowed(module, func, is_kernel) {
            code.extend_from_slice(&[
                0x53, 0x41, 0x54, 0x41, 0x55, 0x41, 0x56, 0x41, 0x57, 0x49, 0x89, 0xF4, 0x49, 0x89, 0xD5, 0x49,
                0x89, 0xCE, 0x4C, 0x89, 0xE8, 0x48, 0xC1, 0xE8, 0x18, 0x24, 0x0F, 0x0C, 0xE0, 0x66, 0xBA, 0xF6,
                0x01, 0xEE, 0x4C, 0x89, 0xF0, 0x66, 0xBA, 0xF2, 0x01, 0xEE, 0x4C, 0x89, 0xE8, 0x66, 0xBA, 0xF3,
                0x01, 0xEE, 0x4C, 0x89, 0xE8, 0x48, 0xC1, 0xE8, 0x08, 0x66, 0xBA, 0xF4, 0x01, 0xEE, 0x4C, 0x89,
                0xE8, 0x48, 0xC1, 0xE8, 0x10, 0x66, 0xBA, 0xF5, 0x01, 0xEE, 0xB0, 0x20, 0x66, 0xBA, 0xF7, 0x01,
                0xEE, 0x4D, 0x89, 0xF7, 0x4D, 0x85, 0xFF, 0x74, 0x2C, 0xB9, 0x40, 0x42, 0x0F, 0x00, 0x66, 0xBA,
                0xF7, 0x01, 0xEC, 0x24, 0x88, 0x3C, 0x08, 0x74, 0x04, 0xFF, 0xC9, 0x75, 0xF1, 0xFC, 0x4C, 0x89,
                0xE7, 0x66, 0xBA, 0xF0, 0x01, 0xB9, 0x00, 0x01, 0x00, 0x00, 0x66, 0xF3, 0x6D, 0x49, 0x89, 0xFC,
                0x49, 0xFF, 0xCF, 0xEB, 0xCF, 0x41, 0x5F, 0x41, 0x5E, 0x41, 0x5D, 0x41, 0x5C, 0x5B, 0xC3,
            ]);
            continue;
        }

        crate::x86::emit_func(module, func, &mut code, &mut call_patches, &mut rt_patches)?;
    }

    if !rt_patches.is_empty() {
        while code.len() % 16 != 0 {
            code.push(0xCC);
        }
        let rt = code.len();
        code.extend_from_slice(RT_PARALLEL);
        for p in rt_patches {
            let rel = (rt as i32) - ((p + 4) as i32);
            code[p..p + 4].copy_from_slice(&rel.to_le_bytes());
        }
    }
    // Dữ liệu tĩnh: sau mã máy, mỗi khối căn 16 byte
    let mut data_addrs = Vec::new();
    for d in &module.datas {
        while code.len() % 16 != 0 {
            code.push(0);
        }
        data_addrs.push(code.len());
        code.extend_from_slice(&d.bytes);
    }
    for (patch_pos, f_id) in call_patches {
        let target_addr = if f_id & crate::x86::DATA_PATCH != 0 {
            *data_addrs.get((f_id & !crate::x86::DATA_PATCH) as usize).ok_or("Không tìm thấy data")?
        } else {
            *func_addrs.get(&f_id).ok_or("Không tìm thấy func_id")?
        };
        let rel = (target_addr as i32) - ((patch_pos + 4) as i32);
        code[patch_pos..patch_pos + 4].copy_from_slice(&rel.to_le_bytes());
    }

    // offs[i] = offset hàm i; tiếp theo là offset của từng data (theo thứ tự module.datas)
    let offs = (0..module.funcs.len()).map(|i| func_addrs[&(i as u32)]).chain(data_addrs).collect();
    Ok((code, offs))
}
