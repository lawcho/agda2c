
module Examples.Pure.Id where

open import Agda.Builtin.Nat

nat-id : Nat → Nat
nat-id n = n

poly-id : ∀{A : Set} → A → A
poly-id a = a

level-poly-id : ∀{ℓ}{A : Set ℓ} → A → A
level-poly-id a = a

module _ (A : Set)  where
    module-id : A → A
    module-id a = a

module _ {ℓ} (A : Set ℓ)  where
    level-module-id : A → A
    level-module-id a = a

