    .text
    .file "addmul_1.S"

#define wp %rdi
#define xp %rsi
#define n_param %edx
#define n %r11d
#define v %rcx

    .section .text.ramp_addmul_1,"ax",@progbits
    .globl ramp_addmul_1
    .align 16, 0x90
    .type ramp_addmul_1,@function
ramp_addmul_1:
    .cfi_startproc

#define L(lbl) .LADDMUL_ ## lbl

    mov n_param, n # Move n away from %rdx

    mov (xp), %rax
    mul v
    add %rax, (wp)
    adc $0, %rdx
    mov %rdx, %r8

    dec n
    jz L(ret)
    add $8, wp
    add $8, xp
    .align 16
L(top):
    mov (xp), %rax
    mul v
    add %r8, %rax
    adc $0, %rdx
    mov %rdx, %r8
    add %rax, (wp)
    adc $0, %r8

    add $8, wp
    add $8, xp
    dec n
    jnz L(top)
L(ret):
    mov %r8, %rax
    ret
L(tmp):
    .size ramp_addmul_1, L(tmp) - ramp_addmul_1
    .cfi_endproc

    .section .text.ramp_submul_1,"ax",@progbits
    .globl ramp_submul_1
    .align 16, 0x90
    .type ramp_submul_1,@function
ramp_submul_1:
    .cfi_startproc

#undef  L
#define L(lbl) .LSUBMUL_ ## lbl

    mov n_param, n # Move n away from %rdx

    mov (xp), %rax
    mul v
    sub %rax, (wp)
    adc $0, %rdx
    mov %rdx, %r8

    dec n
    jz L(ret)
    add $8, wp
    add $8, xp
    .align 16
L(top):
    mov (xp), %rax
    mul v
    add %r8, %rax
    adc $0, %rdx
    mov %rdx, %r8
    sub %rax, (wp)
    adc $0, %r8

    add $8, wp
    add $8, xp
    dec n
    jnz L(top)
L(ret):
    mov %r8, %rax
    ret
L(tmp):
    .size ramp_submul_1, L(tmp) - ramp_submul_1
    .cfi_endproc
