    .text
    .file "sub_n.asm"

    .section .text.ramp_sub_n,"ax",@progbits
    .globl ramp_sub_n
    .align 16, 0x90
    .type ramp_sub_n,@function
ramp_sub_n:
    .cfi_startproc
    #wp = %rdi
    #xp = %rsi
    #yp = %rdx
    #n  = %rcx

    mov %ecx, %eax
    shr $2, %rcx
    and $3, %eax
    jrcxz .Llt4

    mov (%rsi), %r8
    mov 8(%rsi), %r9
    dec %rcx
    jmp .Lmid

.Llt4:
    dec %eax
    mov (%rsi), %r8
    jnz .L2
    sbb (%rdx), %r8
    mov %r8, (%rdi)
    adc %eax, %eax
    ret

.L2:
    dec %eax
    mov 8(%rsi), %r9
    jnz .L3
    sbb (%rdx), %r8
    sbb 8(%rdx), %r9
    mov %r8, (%rdi)
    mov %r9, 8(%rdi)
    adc %eax, %eax
    ret

.L3:
    mov 16(%rsi), %r10
    sbb (%rdx), %r8
    sbb 8(%rdx), %r9
    sbb 16(%rdx), %r10
    mov %r8, (%rdi)
    mov %r9, 8(%rdi)
    mov %r10, 16(%rdi)
    setc %al
    ret

    .align 16
.Ltop:
    sbb (%rdx), %r8
    sbb 8(%rdx), %r9
    sbb 16(%rdx), %r10
    sbb 24(%rdx), %r11
    mov %r8, (%rdi)
    lea 32(%rsi), %rsi
    mov %r9, 8(%rdi)
    mov %r10, 16(%rdi)
    dec %rcx
    mov %r11, 24(%rdi)
    lea 32(%rdx), %rdx
    mov (%rsi), %r8
    mov 8(%rsi), %r9
    lea 32(%rdi), %rdi
.Lmid:
    mov 16(%rsi), %r10
    mov 24(%rsi), %r11
    jnz .Ltop

.Lend:
    lea 32(%rsi), %rsi
    sbb (%rdx), %r8
    sbb 8(%rdx), %r9
    sbb 16(%rdx), %r10
    sbb 24(%rdx), %r11
    lea 32(%rdx), %rdx
    mov %r8, (%rdi)
    mov %r9, 8(%rdi)
    mov %r10, 16(%rdi)
    mov %r11, 24(%rdi)
    lea 32(%rdi), %rdi

    inc %eax
    dec %eax
    jnz .Llt4
    adc %eax, %eax
    ret
.Ltmp:
    .size ramp_sub_n, .Ltmp - ramp_sub_n
    .cfi_endproc
