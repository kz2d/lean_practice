#eval 4
#check (x: Nat) -> Nat

def fib: (x: Nat) -> Nat := fun x =>
    if x == 0
        then x 
    else fib x - 1


#eval fib 5