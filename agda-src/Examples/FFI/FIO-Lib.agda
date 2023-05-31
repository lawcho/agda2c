
-- Library of monad-style helpers
module Examples.FFI.FIO-Lib where

open import Agda.Builtin.List
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

open import Foreign-C.Sugared
    renaming (_>>=_ to _>>='_; _>>_ to _>>'_; ccall to ccall'; exit to exit')
    public

-- FIO adds 'result type' to CSS
FIO : Set → Set
FIO A = (A → CCS) → CCS

-- Monad combinators for FIO
_>>=_ : ∀{A B} → FIO A → (A → FIO B) → FIO B
(~~a >>= a→~~b) b = ~~a λ a → a→~~b a b

pure : ∀{A} → A → FIO A
pure a = λ ~a → ~a a

-- Derived general-purpose monad combinators
_>>_ : ∀{A B} → FIO A → FIO B → FIO B
ma >> mb = ma >>= λ _ → mb

sequenceM : ∀{A} → List (FIO A) → FIO (List A)
sequenceM [] = pure []
sequenceM (mx ∷ mxs) = do
    x ← mx
    xs ← sequenceM mxs
    pure (x ∷ xs)

mapM' : ∀{A B : Set} → (A → FIO B) → List A → FIO ⊤
mapM' f l = sequenceM (map f l) >> pure tt

-- Sugared CCS operations lifted to FIO
lift-cmd : (c : Cmd) → FIO (cmd-ret-ty c)
lift-cmd c _ .head = c
lift-cmd _ ~rc .tail rc = ~rc rc

ccall : ∀ fun-sig → {{Call-Handle fun-sig}}
    → ⟦ arg-tys fun-sig ⟧as→
    FIO ⟦ ret-ty fun-sig ⟧r
ccall fs = convert-⟦⟧as λ as → lift-cmd (cmd 0 (cmd-ccall fs as))

return : ∀{R} → {{Ret-Handle R}} → ⟦ R ⟧r → FIO ⊥
return R _ .head = cmd 1 (cmd-return R)
return R _ .tail ()

-- Eliminator for FIO sugar layer
run : FIO ⊥ → CCS
run ~~⊥ = ~~⊥ λ ()
