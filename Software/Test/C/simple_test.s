.global _start
_start:

    # Arithmetic and logic operations
    li t0, 10         # Load immediate value 10 into t0
    li t1, 20         # Load immediate value 20 into t1
    add t2, t0, t1    # Add t0 and t1, store result in t2
    sub t3, t1, t0    # Subtract t0 from t1, store result in t3
    and t4, t0, t1    # Bitwise AND t0 and t1, store result in t4
    or  t5, t0, t1    # Bitwise OR t0 and t1, store result in t5
    xor t6, t0, t1    # Bitwise XOR t0 and t1, store result in t6
    slt a0, t0, t1    # Set a0 to 1 if t0 is less than t1, else 0

    # Loop
    li a1, 0          # Initialize loop counter
loop:
    addi a1, a1, 1    # Increment loop counter
    bne a1, t0, loop  # If counter not equal to t0, loop again

    # Conditional branch
    beq t0, t1, skip  # If t0 equal to t1, skip next instruction
    li a2, 1          # Set a2 to 1
skip:
    li a2, 2          # Set a2 to 2

    # Function call
    li a3, 5          # Argument for factorial function
    jal ra, factorial # Jump and link register to factorial
    sw a0, 0(sp)      # Save return value from factorial to stack
    j _exit           # Jump to exit

factorial:
    # Factorial function (recursive)
    beqz a3, fact_exit  # If argument is zero, return 1
    addi sp, sp, -4     # Allocate stack space
    sw ra, 0(sp)        # Save return address to stack
    addi a3, a3, -1     # Decrement argument
    jal ra, factorial   # Recursive call
    lw ra, 0(sp)        # Restore return address from stack
    addi sp, sp, 4      # Deallocate stack space
    mul a0, a0, a3      # Multiply result by argument
    ret                 # Return

fact_exit:
    li a0, 1            # Set return value to 1
    ret                 # Return

_exit:
    # Exit