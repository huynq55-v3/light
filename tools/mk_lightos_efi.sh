#!/bin/bash
# mk_lightos_efi.sh <ESP_UUID> <đầu_ra.efi>: dựng GRUB EFI standalone (có sẵn multiboot) với menu Light OS / Ubuntu
set -euo pipefail
D="$(cd "$(dirname "$0")" && pwd)"
CFG=$(mktemp); trap 'rm -f "$CFG"' EXIT
sed "s/@ESP_UUID@/$1/" "$D/lightos-grub.cfg.in" > "$CFG"
grub-mkstandalone -O x86_64-efi -o "$2" \
    --modules="part_gpt fat multiboot all_video efi_gop search search_fs_uuid normal echo chain efifwsetup" \
    "boot/grub/grub.cfg=$CFG"
