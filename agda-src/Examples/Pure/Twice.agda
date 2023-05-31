
-- Minimal example, expected to generate compact C code
module Examples.Pure.Twice where

open import Agda.Builtin.Nat

twice : (Nat → Nat) → Nat → Nat
twice f x = f (f x)
