
-- Syntactic sugar around the Foreign-C library
-- (the compiler does not have special knowledge of this module)

module Foreign-C.Sugared where


-- Re-exports
open import Foreign-C.Core public
open CCS public
open Sig public
open Exposed public

open import Agda.Builtin.List public
open import Agda.Builtin.Bool public
open import Agda.Builtin.Nat public
open import Agda.Builtin.Unit public
open import Agda.Builtin.Sigma public

-- Extra combinators

-- For do-noation
_>>_ : Cmd → CCS → CCS
c >> s = c >>= λ _ → s

-- Variant of ⟦_⟧as using n-ary function rather than pairs
⟦_⟧as→_ : List Arg-Type → Set → Set
⟦ [] ⟧as→ B = B
⟦ a ∷ as ⟧as→ B = ⟦ a ⟧a → ⟦ as ⟧as→ B

-- De-sugaring helper function
convert-⟦⟧as : ∀{as B} → (⟦ as ⟧as → B) → ⟦ as ⟧as→ B
convert-⟦⟧as {as = []} ⊤→B = ⊤→B tt
convert-⟦⟧as {as = a ∷ as} (⟦a⟧×⟦as⟧→B) ⟦a⟧ = convert-⟦⟧as (λ ⟦as⟧ → ⟦a⟧×⟦as⟧→B (⟦a⟧ , ⟦as⟧))

-- Write (ccall x .. z) instead of (cmd 0 (cmd-call (x ∷ ... ∷ z ∷ [])))
ccall : ∀ fun-sig → {{Call-Handle fun-sig}} → ⟦ arg-tys fun-sig ⟧as→ Cmd
ccall fs = convert-⟦⟧as λ as → cmd 0 (cmd-ccall fs as)

-- Write (exit ...) instead of (cmd 1 (cmd-return ...))
exit : ∀ {t} → {{Ret-Handle t}} → ⟦ t ⟧r → Cmd
exit r = cmd 1 (cmd-return r)

{-# INLINE _>>_ #-} -- helps termination checker

-- Not for use by users, just needs to be available to the compiler
import Foreign-C.FFI-Compiler
