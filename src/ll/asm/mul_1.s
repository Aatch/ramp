    .text
    .file "mul_1.asm"

    .section .text.ramp_mul_1,"ax",@progbits
    .globl ramp_mul_1
    .align 16, 0x90
    .type ramp_mul_1,@function
ramp_mul_1:
    .cfi_startproc
    #wp = %rdi
    #xp = %rsi
    #n_param = %rdx
    #n = %r11 - %rdx is used by mul
    #v = %rcx

    mov %edx, %r11d # Move n away from %rdx

    mov (%rsi), %rax
    mul %rcx
    mov %rax, (%rdi)

    dec %r11d
    jz .Lret
    add $8, %rdi
    add $8, %rsi
    mov %rdx, %r8
    .align 16
.Lloop:
    mov (%rsi), %rax
    mul %rcx
    add %r8, %rax
    adc $0, %rdx
    mov %rax, (%rdi)
    add $8, %rdi
    add $8, %rsi
    dec %r11d
    jz .Lret
    mov %rdx, %r8
    jmp .Lloop
.Lret:
    mov %rdx, %rax
    ret
.Ltmp:
    .size ramp_mul_1, .Ltmp - ramp_mul_1
    .cfi_endproc
