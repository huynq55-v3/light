#!/bin/bash
# Cài Light OS lên máy thật (UEFI + GRUB multiboot), dùng lại phân vùng "rustos" và đổi tên thành "lightos".
#
#   sudo bash tools/install_lightos.sh                   # chạy thử: chỉ in kế hoạch, KHÔNG thay đổi gì
#   sudo bash tools/install_lightos.sh --yes             # cài đầy đủ (xóa dữ liệu phân vùng rustos sau khi sao lưu)
#   sudo bash tools/install_lightos.sh --kernel-only --yes   # chỉ cập nhật kernel.elf + bootloader, giữ dữ liệu Light
#   sudo bash tools/install_lightos.sh --disk-only --yes     # chỉ ghi lại disk.img vào phân vùng lightos
#
# Việc làm:
#   1. Sao lưu nội dung phân vùng rustos + thư mục EFI/rustos + /etc/grub.d/40_custom vào ~/lightos_backup_<ngày>/
#   2. Xóa chữ ký ext4, ghi disk.img (LIGHTVFS) vào phân vùng, đặt tên GPT = "lightos"
#   3. ESP: EFI/lightos/kernel.elf + EFI/lightos/lightos.efi (GRUB standalone có sẵn multiboot, menu Light OS/Ubuntu)
#   4. Xóa mục UEFI cũ trỏ vào \EFI\rustos, thêm mục "Light OS" ở CUỐI BootOrder (Ubuntu vẫn khởi động mặc định)
#   5. Thay mục "Rust-only OS" trong /etc/grub.d/40_custom bằng "Light OS" (chainload), chạy update-grub
#
# Yêu cầu: TẮT Secure Boot trong BIOS (HP: F10 -> Advanced/Security -> Secure Boot Configuration). GRUB khóa lệnh
# `multiboot` khi Secure Boot bật, và lightos.efi không được ký.
# Khởi động vào Light OS một lần: sudo efibootmgr -n <số mục "Light OS">; reboot  (hoặc F9 lúc bật máy).
# Trong Light OS: F1..F7 mở App ở ô Dock tương ứng, F12 khởi động lại.

set -euo pipefail

DISK=/dev/nvme0n1
PARTNUM=2
PART=${DISK}p${PARTNUM}
ESPNUM=1
ESP_MNT=/boot/efi
OLD_LABEL=rustos
NEW_NAME=lightos
REPO="$(cd "$(dirname "$0")/.." && pwd)"
KERNEL="$REPO/kernel.elf"
IMG="$REPO/disk.img"

YES=0; MODE=full
for a in "$@"; do
    case "$a" in
        --yes) YES=1 ;;
        --kernel-only) MODE=kernel ;;
        --disk-only) MODE=disk ;;
        *) echo "Tham số không hiểu: $a"; exit 2 ;;
    esac
done

die() { echo "LỖI: $*" >&2; exit 1; }
run() { if [ $YES = 1 ]; then echo "+ $*"; "$@"; else echo "[thử] $*"; fi; }

[ "$(id -u)" = 0 ] || die "cần chạy bằng sudo"
[ -f "$KERNEL" ] && [ -f "$IMG" ] || die "thiếu $KERNEL hoặc $IMG (chạy cargo run --release trước)"
head -c 8 "$IMG" | grep -q LIGHTVFS || die "$IMG không có superblock LIGHTVFS"
[ -b "$PART" ] || die "không có $PART"
findmnt -n -o SOURCE / | grep -q "^$PART\$" && die "$PART là phân vùng gốc của hệ thống!"
mountpoint -q "$ESP_MNT" || die "ESP chưa mount ở $ESP_MNT"
ESP_DEV=$(findmnt -n -o SOURCE "$ESP_MNT")
[ "$ESP_DEV" = "${DISK}p${ESPNUM}" ] || die "ESP là $ESP_DEV, không phải ${DISK}p${ESPNUM}"
ESP_UUID=$(blkid -s UUID -o value "$ESP_DEV")
for t in sgdisk wipefs efibootmgr grub-mkstandalone update-grub partx blockdev; do command -v $t >/dev/null || die "thiếu lệnh $t"; done

LABEL=$(blkid -s LABEL -o value "$PART" 2>/dev/null || true)
PNAME=$(sgdisk -i $PARTNUM $DISK | sed -n "s/^Partition name: '\(.*\)'/\1/p")
if [ "$LABEL" = "$OLD_LABEL" ]; then
    FIRST=1
elif [ "$PNAME" = "$NEW_NAME" ]; then
    FIRST=0
else
    die "$PART không phải phân vùng '$OLD_LABEL' (nhãn='$LABEL') cũng không phải '$NEW_NAME' (tên GPT='$PNAME') — dừng để an toàn"
fi
[ $MODE = full ] || [ $FIRST = 0 ] || die "lần cài đầu phải chạy chế độ đầy đủ (không --kernel-only/--disk-only)"
PSIZE=$(blockdev --getsize64 "$PART")
[ "$PSIZE" -ge "$(stat -c %s "$IMG")" ] || die "phân vùng nhỏ hơn disk.img"

echo "== Light OS installer: chế độ $MODE, phân vùng $PART ($((PSIZE/1048576)) MB, nhãn='$LABEL', tên GPT='$PNAME'), ESP $ESP_DEV ($ESP_UUID)"
[ $YES = 1 ] || echo "== CHẠY THỬ: thêm --yes để thực hiện"

USER_HOME=$(getent passwd "${SUDO_USER:-root}" | cut -d: -f6)
BK="$USER_HOME/lightos_backup_$(date +%Y%m%d_%H%M%S)"

# 1-2. Phân vùng dữ liệu
if [ $MODE = full ] || [ $MODE = disk ]; then
    if [ $FIRST = 1 ]; then
        run mkdir -p "$BK"
        MNT=$(findmnt -n -o TARGET "$PART" | head -1 || true)
        if [ -z "$MNT" ]; then
            MNT=/mnt/rustos_bk; run mkdir -p $MNT; run mount -o ro "$PART" $MNT
        fi
        run tar czf "$BK/rustos_partition.tar.gz" -C "$MNT" .
        [ -d "$ESP_MNT/EFI/rustos" ] && run tar czf "$BK/efi_rustos.tar.gz" -C "$ESP_MNT/EFI" rustos
        run cp /etc/grub.d/40_custom "$BK/40_custom.bak"
    fi
    for m in $(findmnt -n -o TARGET "$PART" || true); do run umount "$m"; done
    run wipefs -a "$PART"
    run dd if="$IMG" of="$PART" bs=1M conv=fsync status=none
    run sgdisk -c $PARTNUM:$NEW_NAME $DISK
    run partx -u $DISK
fi

# 3. Bootloader + kernel trên ESP
if [ $MODE = full ] || [ $MODE = kernel ]; then
    run mkdir -p "$ESP_MNT/EFI/lightos"
    run cp "$KERNEL" "$ESP_MNT/EFI/lightos/kernel.elf"
    run bash "$REPO/tools/mk_lightos_efi.sh" "$ESP_UUID" "$ESP_MNT/EFI/lightos/lightos.efi"
fi

# 4-5. Mục khởi động
if [ $MODE = full ]; then
    if [ -d "$ESP_MNT/EFI/rustos" ]; then run rm -rf "$ESP_MNT/EFI/rustos"; fi
    for n in $(efibootmgr -v | grep -i 'EFI\\rustos' | sed -n 's/^Boot\([0-9A-Fa-f]\{4\}\).*/\1/p'); do
        run efibootmgr -q -b "$n" -B
    done
    if ! efibootmgr | grep -q 'Light OS'; then
        run efibootmgr -q -c -d $DISK -p $ESPNUM -L "Light OS" -l '\EFI\lightos\lightos.efi'
    fi
    # efibootmgr -c đặt mục mới lên ĐẦU BootOrder -> chuyển xuống cuối. BootOrder của HP có thể chứa số không tồn tại
    # (vd 2002, 2004) mà efibootmgr -o từ chối -> chỉ giữ các mục có thật.
    NEW=$(efibootmgr | sed -n 's/^Boot\([0-9A-Fa-f]\{4\}\)\* Light OS.*/\1/p' | head -1)
    if [ -n "${NEW:-}" ]; then
        EXIST=$(efibootmgr | sed -n 's/^Boot\([0-9A-Fa-f]\{4\}\)\*\{0,1\} .*/\1/p')
        ORDER=""
        for e in $(efibootmgr | sed -n 's/^BootOrder: //p' | tr ',' ' '); do
            [ "$e" = "$NEW" ] && continue
            echo "$EXIST" | grep -qx "$e" && ORDER="$ORDER${ORDER:+,}$e"
        done
        run efibootmgr -q -o "$ORDER${ORDER:+,}$NEW"
    fi
    if grep -q 'Rust-only OS' /etc/grub.d/40_custom || ! grep -q 'Light OS' /etc/grub.d/40_custom; then
        NEWC=$(mktemp)
        cat > "$NEWC" <<EOF
#!/bin/sh
exec tail -n +3 \$0
# This file provides an easy way to add custom menu entries.  Simply type the
# menu entries you want to add after this comment.  Be careful not to change
# the 'exec tail' line above.

menuentry "Light OS" {
    insmod part_gpt
    insmod fat
    insmod chain
    search --no-floppy --fs-uuid --set=root $ESP_UUID
    chainloader /EFI/lightos/lightos.efi
}
EOF
        run install -m 755 "$NEWC" /etc/grub.d/40_custom
        rm -f "$NEWC"
        run update-grub
    fi
fi

echo "== Xong."
if [ $YES = 1 ]; then
    [ $FIRST = 1 ] && [ $MODE = full ] && echo "Sao lưu: $BK"
    NUM=$(efibootmgr | sed -n 's/^Boot\([0-9A-Fa-f]\{4\}\)\* Light OS.*/\1/p' | head -1)
    echo "Khởi động vào Light OS một lần:  sudo efibootmgr -n $NUM && reboot"
    echo "Secure Boot phải TẮT. Trong Light OS: F1/F2 mở App, F12 khởi động lại (về Ubuntu)."
fi
