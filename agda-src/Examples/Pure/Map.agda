
module Examples.Pure.Map where

open import Agda.Builtin.List

map : {A B : Set} → (A → B) → List A → List B
map _ [] = []
map f (x ∷ l) = f x ∷ map f l
