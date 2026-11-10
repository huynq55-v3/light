# Bộ xử lý exception 0..31 (nằm trong ảnh ELF kernel, IDT trỏ thẳng vào đây).
# Mỗi stub 16 byte: đẩy mã lỗi giả 0 nếu CPU không đẩy, đẩy số vector, nhảy về exc_common.
# exc_common gọi hàm Light `kernel_panic(io_ghost, vec, err, rip, cr2, apic)` qua địa chỉ tại [0x8FF8]
# (boot code ghi vào). Cờ [0x8FF0] chống panic lồng nhau: lần panic thứ hai chỉ dừng máy.
    .intel_syntax noprefix
    .text
    .globl exc_stubs
exc_stubs:
    .balign 16
    push 0
    push 0
    jmp exc_common
    .balign 16
    push 0
    push 1
    jmp exc_common
    .balign 16
    push 0
    push 2
    jmp exc_common
    .balign 16
    push 0
    push 3
    jmp exc_common
    .balign 16
    push 0
    push 4
    jmp exc_common
    .balign 16
    push 0
    push 5
    jmp exc_common
    .balign 16
    push 0
    push 6
    jmp exc_common
    .balign 16
    push 0
    push 7
    jmp exc_common
    .balign 16
    push 8
    jmp exc_common
    .balign 16
    push 0
    push 9
    jmp exc_common
    .balign 16
    push 10
    jmp exc_common
    .balign 16
    push 11
    jmp exc_common
    .balign 16
    push 12
    jmp exc_common
    .balign 16
    push 13
    jmp exc_common
    .balign 16
    push 14
    jmp exc_common
    .balign 16
    push 0
    push 15
    jmp exc_common
    .balign 16
    push 0
    push 16
    jmp exc_common
    .balign 16
    push 17
    jmp exc_common
    .balign 16
    push 0
    push 18
    jmp exc_common
    .balign 16
    push 0
    push 19
    jmp exc_common
    .balign 16
    push 0
    push 20
    jmp exc_common
    .balign 16
    push 21
    jmp exc_common
    .balign 16
    push 0
    push 22
    jmp exc_common
    .balign 16
    push 0
    push 23
    jmp exc_common
    .balign 16
    push 0
    push 24
    jmp exc_common
    .balign 16
    push 0
    push 25
    jmp exc_common
    .balign 16
    push 0
    push 26
    jmp exc_common
    .balign 16
    push 0
    push 27
    jmp exc_common
    .balign 16
    push 0
    push 28
    jmp exc_common
    .balign 16
    push 29
    jmp exc_common
    .balign 16
    push 30
    jmp exc_common
    .balign 16
    push 0
    push 31
    jmp exc_common
    .balign 16
exc_common:
    cli
    lock bts qword ptr [0x8FF0], 0
    jc 2f
    mov eax, 1
    cpuid
    shr ebx, 24
    mov r9, rbx                  # APIC ID
    mov rsi, [rsp]               # vector
    mov rdx, [rsp+8]             # mã lỗi
    mov rcx, [rsp+16]            # RIP lúc lỗi
    mov r8, cr2                  # địa chỉ gây #PF
    xor edi, edi                 # thẻ io<0,0xffff> là kiểu ghost: giá trị không quan trọng
    and rsp, -16
    mov rax, [0x8FF8]
    test rax, rax
    jz 2f
    call rax
2:  cli
    hlt
    jmp 2b
