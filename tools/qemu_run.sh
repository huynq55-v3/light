#!/usr/bin/env bash
# Chạy Light OS trong QEMU có cửa sổ (kernel.elf + đĩa LightFS chứa các App).
#   bash tools/qemu_run.sh            # dùng lại đĩa làm việc (giữ file đã tạo trong Light OS giữa các lần chạy)
#   bash tools/qemu_run.sh --fresh    # chép lại đĩa sạch từ disk.img (sau khi build lại App)
#   bash tools/qemu_run.sh --usb      # bàn phím + chuột USB (xHCI) thay cho PS/2
# Biến môi trường: QEMU_MEM (mặc định 4G), QEMU_SMP (mặc định 4).
# Serial của Light OS in ra terminal này. Thoát: đóng cửa sổ, hoặc Ctrl+Alt+G để nhả chuột.
set -euo pipefail
R="$(cd "$(dirname "$0")/.." && pwd)"
DISK="$R/target/qemu_disk.img"
FRESH=0; USB=0
for a in "$@"; do
    case "$a" in
        --fresh) FRESH=1 ;;
        --usb) USB=1 ;;
        *) echo "tham số lạ: $a" >&2; exit 1 ;;
    esac
done
[ -f "$R/kernel.elf" ] && [ -f "$R/disk.img" ] || { echo "chưa build: cargo run --release --bin light" >&2; exit 1; }
mkdir -p "$R/target"
if [ "$FRESH" = 1 ] || [ ! -f "$DISK" ] || [ "$R/disk.img" -nt "$DISK" ]; then
    cp "$R/disk.img" "$DISK"
    echo "đĩa làm việc: chép mới từ disk.img"
fi
truncate -s 64M "$DISK"
ACCEL=()
[ -w /dev/kvm ] && ACCEL=(-enable-kvm -cpu host)
DEV=()
if [ "$USB" = 1 ]; then
    DEV=(-machine pc,i8042=off,vmport=off -device qemu-xhci,id=xhci -device usb-kbd,bus=xhci.0 -device usb-mouse,bus=xhci.0)
fi
exec qemu-system-x86_64 "${ACCEL[@]}" -m "${QEMU_MEM:-4G}" -smp "${QEMU_SMP:-4}" \
    -kernel "$R/kernel.elf" -drive "file=$DISK,format=raw,if=ide" \
    "${DEV[@]}" -serial stdio
