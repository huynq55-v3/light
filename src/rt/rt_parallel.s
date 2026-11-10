# Runtime fork-join cho lệnh `parallel` (nhúng vào mã máy mỗi module có dùng parallel).
# ABI SysV: rdi = bảng SMP (0x7e000), rsi = n (1..16), rdx = địa chỉ hàm worker,
#           rcx = base, r8 = stride (byte mỗi phần), r9 = arg
# Hàm worker: f(rdi = base + i*stride, rsi = arg, rdx = i)
# Bảng SMP: slot c (c = 1..15, 32 byte tại 0x7e000 + c*32) = [fn, slice, arg, idx/result];
#           slot 0: [0] = số nhân logic - 1, [1] = cờ AVX2, [2] = bitmask AP đã online (bit c)
# Phần i chạy trên AP có APIC ID = i nếu AP đó đã online, ngược lại chạy ngay trên nhân gọi.
# Trả về khi TẤT CẢ các phần đã xong -> hàm cha không bao giờ thấy worker còn chạy.
    .intel_syntax noprefix
    .text
    .globl lt_parallel
lt_parallel:
    push rbx
    push rbp
    push r12
    push r13
    push r14
    push r15
    sub rsp, 24                  # [rsp] = i, [rsp+8] = bitmask các phần đã giao cho AP; căn 16 byte
    mov r12, rdi
    mov r13, rsi
    mov r14, rdx
    mov r15, rcx
    mov rbx, r8
    mov rbp, r9
    mov qword ptr [rsp+8], 0
    mov qword ptr [rsp], 1
1:  mov rax, [rsp]               # Pha 1: giao phần 1..n-1 cho các AP đang online
    cmp rax, r13
    jae 4f
    bt qword ptr [r12+16], rax
    jnc 3f
    mov rcx, rax
    shl rcx, 5
    add rcx, r12
2:  pause                        # chờ slot rảnh (phòng hờ)
    cmp qword ptr [rcx], 0
    jne 2b
    mov rdx, rax
    imul rdx, rbx
    add rdx, r15
    mov [rcx+8], rdx
    mov [rcx+16], rbp
    mov [rcx+24], rax
    mov [rcx], r14               # ghi fn sau cùng: AP chỉ bắt đầu khi thấy fn != 0
    bts qword ptr [rsp+8], rax
    mov edx, 0xFEE00300
5:  test dword ptr [rdx], 0x1000 # chờ ICR rảnh (delivery status)
    jnz 5b
    mov ecx, eax
    shl ecx, 24
    mov dword ptr [rdx+0x10], ecx
    mov dword ptr [rdx], 0x4040  # Fixed IPI vector 0x40 tới APIC ID = i
3:  inc qword ptr [rsp]
    jmp 1b
4:  mov rdi, r15                 # Pha 2: phần 0 chạy ngay trên nhân gọi
    mov rsi, rbp
    xor edx, edx
    call r14
    mov qword ptr [rsp], 1
6:  mov rax, [rsp]               # Pha 3: chờ phần đã giao, tự chạy phần chưa giao
    cmp rax, r13
    jae 9f
    bt qword ptr [rsp+8], rax
    jnc 8f
    mov rcx, rax
    shl rcx, 5
    add rcx, r12
7:  pause
    cmp qword ptr [rcx], 0
    jne 7b
    jmp 10f
8:  mov rdi, rax
    imul rdi, rbx
    add rdi, r15
    mov rsi, rbp
    mov rdx, rax
    call r14
10: inc qword ptr [rsp]
    jmp 6b
9:  add rsp, 24
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbp
    pop rbx
    ret
