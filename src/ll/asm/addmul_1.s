    .text
    .file "addmul_1.asm"

    .section .text.ramp_addmul_1,"ax",@progbits
    .globl ramp_addmul_1
    .align 16, 0x90
    .type ramp_addmul_1,@function
ramp_addmul_1:
    .cfi_startproc
    #wp = %rdi
    #xp = %rsi
    #n_param = %rdx
    #n = %r11 - %rdx is used by mul
    #v = %rcx

    mov %edx, %r11d # Move n away from %rdx

    mov (%rsi), %rax
    mul %rcx
    add %rax, (%rdi)
    adc $0, %rdx
    mov %rdx, %r8

    dec %r11d
    jz .Lret
    add $8, %rdi
    add $8, %rsi
    .align 16
.Lloop:
    mov (%rsi), %rax
    mul %rcx
    add %r8, %rax
    adc $0, %rdx
    mov %rdx, %r8
    add %rax, (%rdi)
    adc $0, %r8

    add $8, %rdi
    add $8, %rsi
    dec %r11d
    jnz .Lloop
.Lret:
    mov %r8, %rax
    ret
.Ltmp:
    .size ramp_addmul_1, .Ltmp - ramp_addmul_1
    .cfi_endproc
