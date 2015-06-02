    .text
    .file "addsub_n.S"

#define wp %rdi
#define xp %rsi
#define yp %rdx
#define n %rcx

    .section .text.ramp_add_n,"ax",@progbits
    .globl ramp_add_n
    .align 16, 0x90
    .type ramp_add_n,@function
ramp_add_n:
    .cfi_startproc

#define L(lbl) .LADD_ ## lbl

    mov %ecx, %eax
    shr $2, n
    and $3, %eax
    jrcxz L(lt4)

    mov (xp), %r8
    mov 8(xp), %r9
    dec n
    jmp L(mid)

L(lt4):
    dec %eax
    mov (xp), %r8
    jnz L(2)
    adc (yp), %r8
    mov %r8, (wp)
    adc %eax, %eax
    ret

L(2):
    dec %eax
    mov 8(xp), %r9
    jnz L(3)
    adc (yp), %r8
    adc 8(yp), %r9
    mov %r8, (wp)
    mov %r9, 8(wp)
    adc %eax, %eax
    ret

L(3):
    mov 16(xp), %r10
    adc (yp), %r8
    adc 8(yp), %r9
    adc 16(yp), %r10
    mov %r8, (wp)
    mov %r9, 8(wp)
    mov %r10, 16(wp)
    setc %al
    ret

    .align 16
L(top):
    adc (yp), %r8
    adc 8(yp), %r9
    adc 16(yp), %r10
    adc 24(yp), %r11
    mov %r8, (wp)
    lea 32(xp), xp
    mov %r9, 8(wp)
    mov %r10, 16(wp)
    dec n
    mov %r11, 24(wp)
    lea 32(yp), yp
    mov (xp), %r8
    mov 8(xp), %r9
    lea 32(wp), %rdi
L(mid):
    mov 16(xp), %r10
    mov 24(xp), %r11
    jnz L(top)

L(end):
    lea 32(xp), xp
    adc (yp), %r8
    adc 8(yp), %r9
    adc 16(yp), %r10
    adc 24(yp), %r11
    lea 32(yp), yp
    mov %r8, (wp)
    mov %r9, 8(wp)
    mov %r10, 16(wp)
    mov %r11, 24(wp)
    lea 32(wp), wp

    inc %eax
    dec %eax
    jnz L(lt4)
    adc %eax, %eax
    ret
L(tmp):
    .size ramp_add_n, L(tmp) - ramp_add_n
    .cfi_endproc

    .section .text.ramp_sub_n,"ax",@progbits
    .globl ramp_sub_n
    .align 16, 0x90
    .type ramp_sub_n,@function
ramp_sub_n:
    .cfi_startproc

#undef L
#define L(lbl) .LSUB_ ## lbl

    mov %ecx, %eax
    shr $2, n
    and $3, %eax
    jrcxz L(lt4)

    mov (xp), %r8
    mov 8(xp), %r9
    dec n
    jmp L(mid)

L(lt4):
    dec %eax
    mov (xp), %r8
    jnz L(2)
    sbb (yp), %r8
    mov %r8, (wp)
    adc %eax, %eax
    ret

L(2):
    dec %eax
    mov 8(xp), %r9
    jnz L(3)
    sbb (yp), %r8
    sbb 8(yp), %r9
    mov %r8, (wp)
    mov %r9, 8(wp)
    adc %eax, %eax
    ret

L(3):
    mov 16(xp), %r10
    sbb (yp), %r8
    sbb 8(yp), %r9
    sbb 16(yp), %r10
    mov %r8, (wp)
    mov %r9, 8(wp)
    mov %r10, 16(wp)
    setc %al
    ret

    .align 16
L(top):
    sbb (yp), %r8
    sbb 8(yp), %r9
    sbb 16(yp), %r10
    sbb 24(yp), %r11
    mov %r8, (wp)
    lea 32(xp), xp
    mov %r9, 8(wp)
    mov %r10, 16(wp)
    dec n
    mov %r11, 24(wp)
    lea 32(yp), yp
    mov (xp), %r8
    mov 8(xp), %r9
    lea 32(wp), %rdi
L(mid):
    mov 16(xp), %r10
    mov 24(xp), %r11
    jnz L(top)

L(end):
    lea 32(xp), xp
    sbb (yp), %r8
    sbb 8(yp), %r9
    sbb 16(yp), %r10
    sbb 24(yp), %r11
    lea 32(yp), yp
    mov %r8, (wp)
    mov %r9, 8(wp)
    mov %r10, 16(wp)
    mov %r11, 24(wp)
    lea 32(wp), wp

    inc %eax
    dec %eax
    jnz L(lt4)
    adc %eax, %eax
    ret
L(tmp):
    .size ramp_sub_n, L(tmp) - ramp_sub_n
    .cfi_endproc
