#!/bin/sh
# Sinh lại các blob mã máy runtime từ mã nguồn assembly (chỉ cần khi sửa *.s). Yêu cầu: binutils.
set -e
cd "$(dirname "$0")"
for f in rt_parallel rt_exc; do
    as --64 -o "/tmp/$f.o" "$f.s"
    objcopy -O binary -j .text "/tmp/$f.o" "$f.bin"
done
nm /tmp/rt_exc.o | grep exc_common
