	.att_syntax
	.text
	.p2align	5
	.global	hachi_jazz_mul_hi_u64
	.type	hachi_jazz_mul_hi_u64, %function
hachi_jazz_mul_hi_u64:
	movq	%rdi, %rdx
	mulxq	%rsi, %rcx, %rax
	ret
	.ident	"Jasmin Compiler 2026.03.2"
	.section	".note.GNU-stack", "", %progbits
