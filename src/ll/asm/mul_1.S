    .text
    .file "mul_1.S"

#define wp %rdi
#define xp %rsi
#define n_param %edx
#define n %r11d
#define v %rcx

    .section .text.ramp_mul_1,"ax",@progbits
    .globl ramp_mul_1
    .align 16, 0x90
    .type ramp_mul_1,@function
ramp_mul_1:
    .cfi_startproc

#define L(lbl) .LMUL_ ## lbl

    mov n_param, n # Move n away from %rdx

    mov (xp), %rax
    mul v
    mov %rax, (wp)

    dec n
    jz L(ret)
    add $8, wp
    add $8, xp
    mov %rdx, %r8
    .align 16
L(top):
    mov (xp), %rax
    mul v
    add %r8, %rax
    adc $0, %rdx
    mov %rax, (wp)
    add $8, wp
    add $8, xp
    dec n
    jz L(ret)
    mov %rdx, %r8
    jmp L(top)
L(ret):
    mov %rdx, %rax
    ret
L(tmp):
    .size ramp_mul_1, L(tmp) - ramp_mul_1
    .cfi_endproc
