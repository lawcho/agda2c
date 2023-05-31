
module Examples.Pure.Fibonacci where

open import Agda.Builtin.Nat

fib : Nat → Nat
fib 0 = 1
fib 1 = 1
fib (suc (suc n)) = fib (suc n) + fib n
