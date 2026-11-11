#!/usr/bin/env bash
# Chạy Light OS trong QEMU có cửa sổ (kernel.elf + đĩa LightFS chứa các App).
#   bash tools/qemu_run.sh            # dùng lại đĩa làm việc (giữ file đã tạo trong Light OS giữa các lần chạy)
#   bash tools/qemu_run.sh --fresh    # chép lại đĩa sạch từ disk.img (sau khi build lại App)
#   bash tools/qemu_run.sh --usb      # bàn phím + chuột USB (xHCI) thay cho PS/2
#   bash tools/qemu_run.sh --agent    # COM1 thành socket target/light_serial.sock cho kênh Agent (tools/light_mcp.py)
#   bash tools/qemu_run.sh --headless # không mở cửa sổ (dùng kèm --agent)
# Biến môi trường: QEMU_MEM (mặc định 4G), QEMU_SMP (mặc định 4).
# Serial của Light OS in ra terminal này. Thoát: đóng cửa sổ, hoặc Ctrl+Alt+G để nhả chuột.
set -euo pipefail
R="$(cd "$(dirname "$0")/.." && pwd)"
DISK="$R/target/qemu_disk.img"
FRESH=0; USB=0; AGENT=0; HEADLESS=0
for a in "$@"; do
    case "$a" in
        --fresh) FRESH=1 ;;
        --usb) USB=1 ;;
        --agent) AGENT=1 ;;
        --headless) HEADLESS=1 ;;
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
SER=(-serial stdio)
if [ "$AGENT" = 1 ]; then
    SOCK="${LIGHT_SERIAL:-$R/target/light_serial.sock}"
    rm -f "$SOCK"
    SER=(-serial "unix:$SOCK,server,nowait")
    echo "kênh Agent: $SOCK  (thử: python3 tools/light_mcp.py --run help)"
fi
[ "$HEADLESS" = 1 ] && DEV+=(-display none)
exec qemu-system-x86_64 "${ACCEL[@]}" -m "${QEMU_MEM:-4G}" -smp "${QEMU_SMP:-4}" \
    -kernel "$R/kernel.elf" -drive "file=$DISK,format=raw,if=ide" \
    "${DEV[@]}" "${SER[@]}"
