.globl main
.data
  #all the text pro mpts that will be needed later
  prompt: .asciiz "Please enter a positive integer: "
  output1: .asciiz "The value of factorial "
  output2: .asciiz " is: "
.text
main:
	#System.out.println("Please enter a positive integer: ")
	#load prompt
	la $a0, prompt 
	#call print string method
	jal printString
	
	#Scanner.nextInt()
	#system call to read integer input
	li $v0, 5
	syscall
	#int gets placed in v0 (temporary) so move it to s0 (saved)
	move $s0, $v0
	
	# expand the stack by 8
	addi $sp, $sp, -8
	#store the int
	sw $s0, ($sp)
	# store return address for later
	sw $ra, 8($sp)
	# call factorial(number)
	jal factorial

	# return the return value
	lw $t0, 4($sp)

	#System.out.print("The value of factorial ")
	# print result
        la $a0, output1
	jal printString
	
	#System.out.print(user entered int which is at 0 on the stack)
	la $a0, ($s0)
	jal printInt
	
	#System.out.print(" is: ")
	la $a0, output2
	#jal = jump and link (Address of following instruction put in $ra,and jump to target address)
	jal printString
	
	#System.out.print(final value which is located at 0 at t0)
	la $a0, ($t0)
	jal printInt
	
	# system call 10 = exit
	li $v0, 10
	# return 0
	li $a0, 0
	syscall

#string argument has to be in $a0
printString:
	#system call 4 is print string
	li $v0, 4
	syscall
	li $v0, 0
	# jr=jump to specify register. $ra=return address
	jr $ra
	
#int argument has to be in $a0
printInt:
	#system call 1 is print int
	li $v0, 1
	syscall
	li $v0, 0
	jr $ra
	
#factorial method
#  ($sp) holds the user entered integer
# 4($sp) holds the return value
# 8($sp) holds the return address
factorial:
	# check base case
	lw $t0, ($sp)
	#  branch to baseCase if  $t0 = 0
	beq $t0, 0, baseCase
	
	# otherwise subtract 1 to represent the next factorial value to multiply
	addi $t0, $t0, -1

	# adjust the stack to make room for the argument, return value, and return address
	addi $sp, $sp, -12
	# store int (after being subtracted by 1)
	# 0($sp) = $t0
	sw $t0, ($sp)
	# store return address
	# 8($sp) = $ra
	sw $ra, 8($sp)
	#recursion 
	jal factorial

	# 4($sp) should contain the returned result after factorial is called
	# $t1 = 4($sp)
	lw $t1, 4($sp)
	# 8($sp) should contain the current return address in the recursive call
	lw $ra, 8($sp)
	# 12($sp) should contain the previous returned result
	lw $t2, 12($sp)

	# readust the stack back
	addi $sp, $sp, 12
	
	# multiply the current result with the previous result
	mult $t1, $t2
	
	# retrieve result of t1 * t2
	mflo $t3
	
	# store as next result in stack
	sw $t3, 4($sp)
	
	#jump to return address in $ra
	jr $ra

#Base case helper method
baseCase:
	# return 1 in the stack
	li      $t0, 1
	sw      $t0, 4($sp)
	jr      $ra
