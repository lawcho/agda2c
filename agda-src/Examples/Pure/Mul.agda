
module Examples.Pure.Mul where

open import Agda.Builtin.Nat

mul : Nat → Nat → Nat
mul zero n = zero
mul 1 n = n
mul (suc m) n = n + mul m n
