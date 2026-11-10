#!/bin/bash
# qemu_uefi_nvme.sh [thư_mục_tạm]: chạy Light OS giống hệt trên laptop — OVMF (UEFI) -> lightos.efi (GRUB, cùng cấu hình
# với tools/install_lightos.sh) -> multiboot -> kernel; đĩa NVMe có GPT: p1 ESP, p2 "lightos" (disk.img), p3 "ubuntu"
# (điền mẫu để phát hiện ghi lạc). Mở cửa sổ QEMU; F1/F2 mở App, F12 khởi động lại.
set -euo pipefail
R="$(cd "$(dirname "$0")/.." && pwd)"
W="${1:-$(mktemp -d)}"; mkdir -p "$W"; cd "$W"
rm -f gpt.img esp.part; truncate -s 256M gpt.img
sgdisk -Z gpt.img >/dev/null
sgdisk -n 1:2048:+64M -t 1:ef00 -c 1:EFI -n 2:0:+64M -t 2:8300 -c 2:lightos -n 3:0:0 -t 3:8300 -c 3:ubuntu gpt.img >/dev/null
first() { sgdisk -i "$1" gpt.img | awk '/First sector/{print $3}'; }
truncate -s 64M esp.part; mformat -i esp.part -F -N 1234abcd ::
mmd -i esp.part ::/EFI ::/EFI/BOOT ::/EFI/lightos
bash "$R/tools/mk_lightos_efi.sh" 1234-ABCD lightos.efi
mcopy -i esp.part lightos.efi ::/EFI/BOOT/BOOTX64.EFI
mcopy -i esp.part lightos.efi ::/EFI/lightos/lightos.efi
mcopy -i esp.part "$R/kernel.elf" ::/EFI/lightos/kernel.elf
dd if=esp.part of=gpt.img bs=512 seek="$(first 1)" conv=notrunc status=none
dd if="$R/disk.img" of=gpt.img bs=512 seek="$(first 2)" conv=notrunc status=none
cp /usr/share/OVMF/OVMF_VARS_4M.fd vars.fd
echo "Ảnh đĩa: $W/gpt.img"
exec qemu-system-x86_64 -enable-kvm -cpu host -m 4G -smp 8 \
  -drive if=pflash,format=raw,readonly=on,file=/usr/share/OVMF/OVMF_CODE_4M.fd -drive if=pflash,format=raw,file=vars.fd \
  -drive if=none,id=nv,file=gpt.img,format=raw -device nvme,drive=nv,serial=light01,bootindex=1 \
  -serial stdio "${@:2}"
