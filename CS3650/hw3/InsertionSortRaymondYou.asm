.data
message1:	.asciiz "Initial array is:\n"			
message2:	.asciiz "Insertion sort is finished!\n"		
openBracket:	.asciiz "[ "					
closeBracket: 	.asciiz" ]\n"					
space: 		.asciiz " "					
		.align 5					
dataName:	.asciiz "Joe"
		.align 5
		.asciiz "Jenny"
		.align 5
		.asciiz "Jill"
		.align 5
		.asciiz "John"
		.align 5
		.asciiz "Jeff"
		.align 5
		.asciiz "Joyce"
		.align 5
		.asciiz "Jerry"
		.align 5
		.asciiz "Janice"
		.align 5
		.asciiz "Jake"
		.align 5
		.asciiz "Jonna"
		.align 5
		.asciiz "Jack"
		.align 5
		.asciiz "Jocelyn"
		.align 5
		.asciiz "Jessie"
		.align 5
		.asciiz "Jess"
		.align 5
		.asciiz "Janet"
		.align 5
		.asciiz "Jane"
		.align 2
dataAddr:	.space 64
size:		.word 16
		.text
		
main:		# load the array into $t0
		la $t0, dataName
		# load data address to #t1
		la $t1, dataAddr
		# load address size to $t2
		la $t2, size	
		# load $t2
		lw $t2, ($t2)
		# load immediate into $t3	
		li $t3, 0
			
initLoop: 	# store $t0 into $t3 data address
		sw $t0, dataAddr($t3)	
		# increment by 4
		addi $t3, $t3, 4
		#increment by 32
		addi $t0, $t0, 32
		# subtract -1 for next loop
		addi $t2, $t2, -1
		# if $t2 > 0, go to initLoop
		bgtz $t2, initLoop
		
		# printf("Initial array is:\n");
		la $a0, message1		
		li $v0, 4
		syscall
		
		# printArray(data, size); 
		la $a0, dataAddr
		la $a1, size
		lw $a1, ($a1)
		jal printArray
		
		# insertSort(data, size);
		la $a0, dataAddr
		la $a1, size
		lw $a1, ($a1)
		jal insertSort
		
		# printf("Insertion sort is finished!\n");
		la $a0, message2
		li $v0, 4
		syscall
		
		# printArray(data, size);
		la $a0, dataAddr
		la $a1, size
		lw $a1, ($a1)
		jal printArray
		
		# exit
		li $v0, 10		
		syscall

str_lt:		# open call frame
		addi $sp, $sp, -4
		# save address
		sw $ra, ($sp)
		# $s1 = $t4
		move $s1, $t4
		# $s2 = $t5
		move $s2, $t5
	str_ltLoop:	# for (*x!='\0' && *y!='\0'; x++, y++)
			#load first byte
			lb $s3, ($s1)
			#load second byte
			lb $s4, ($s2)
			# if $s3 = 0, jump to str_ltEnd
			beqz $s3, str_ltEnd
			# if $s4 = 0, jump to str_ltEnd
			beqz $s4, str_ltEnd
			# if (*x < *y) return 1
			blt $s3, $s4, one
			# if (*y < *x) return 0
			blt $s4, $s3, zero
			# add immediate 1 to $s1
			addi $s1, $s1, 1
			# add immediate 1 to $s2		
			addi $s2, $s2, 1
			j str_ltLoop
	str_ltEnd:	# if $s3 = 0, jump to zero
			beqz $s3, zero			
			# else return 1
	one:		# load immediate 1
			li $v0, 1			
			j end
	zero:		# load immediate 0
			li $v0, 0			
	end: 	# restore return address
		lw $ra, ($sp)
		# free call frame				
		addi $sp, $sp, 4
		# jump return			
		jr $ra					
	
insertSort: 	# $t0 = $a0
		move $t0, $a0		
		# $t1 = $a1
		move $t1, $a1		
		# open call frame
		addi $sp, $sp, -4	
		# save return address
		sw $ra, ($sp)		
		# i, $t2 = 1
		li $t2, 1
	# for(i = 1; i < length; i++)
	outerLoop:	
			# if $t2 >= $t1, go to endOuterLoop
			bge $t2, $t1, endOuterLoop
			# char *value = a[i];
			# j= i-1
			addi $t3, $t2, -1
			# set 4bytes
			mul $s0, $t2, 4		
			# *value = a[i]	
			add $s0, $s0, $t0
			# load word in $s0 to $t4		
			lw $t4, ($s0)
		# for (j = i-1; j >= 0 && str_lt(value, a[j]); j--)			
		innerLoop:	
				# if j < 0, go to endInnerLoop
				bltz $t3, endInnerLoop	
				# set 4 bytes
				mul $s0, $t3, 4		
				# get a[j]
				add $s0, $s0, $t0	
				# load word to $t5
				lw $t5, ($s0)		
				# jump and link to str_lt
				jal str_lt
				# if $v0 = 0, go to endInnerLoop		
				beqz $v0, endInnerLoop	
				# j+1
				addi $s0, $t3, 1	
				# set 4 bytes
				mul $s0, $s0, 4		
				# get a[j+1]
				add $s0, $s0, $t0	
				# a[j+1] = a[j];
				# set $t5 to a[j]
				sw $t5, ($s0)
				# j--	
				addi $t3, $t3, -1	
				j innerLoop
		# a[j+1] = value;
		endInnerLoop:	
				# j+1
				addi $s0, $t3, 1	
				# set 4 bytes
				mul $s0, $s0, 4		
				# get a[j+1]
				add $s0, $s0, $t0	
				# store $t4 
				sw $t4, ($s0)		
				# i++
				addi $t2, $t2, 1	
				j outerLoop
	endOuterLoop: 	# restore return address
			lw $ra, ($sp)			
			# open call frame
			addi $sp, $sp, 4		
			jr $ra
			

	
printArray: 	# $t0 = $a0
		move $t0, $a0
		# int i=0;
		li $t1, 0
		# printf("[ ");	
		la $a0, openBracket
		li $v0, 4
		syscall
	# while(i < size) 
	loop:	# if $t1 > $a1, go to endLoop
		bge $t1, $a1, endLoop
		# printf("  %s", a[i++]);
		lw $a0, ($t0)
		li $v0, 4
		syscall
		la $a0, space
		li $v0, 4
		syscall
		# add space
		addi $t0, $t0, 4
		# add for next loop	
		addi $t1, $t1, 1	
		j loop
	# printf(" ]\n");
	endLoop:
		la $a0, closeBracket		
		li $v0, 4
		syscall
		jr $ra
	
