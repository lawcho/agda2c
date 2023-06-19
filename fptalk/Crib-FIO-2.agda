
-- https://wokwi.com/projects/343960210261410387

open import Foreign-C.Sugared
    renaming (_>>=_ to _>>='_; _>>_ to _>>'_; ccall to ccall'; exit to exit')

imp = "#include<pico/stdlib.h>"
{-# COMPILE RAW_C imp #-}

put = sig void "gpio_put_all" (uint16 ∷ [])
init = sig void "gpio_init" (uint16 ∷ [])
dir = sig void "gpio_set_dir" (uint16 ∷ bool ∷ [])
sleep = sig void "sleep_ms" (uint16 ∷ [])


-- C-P style
FIO : Set → Set
FIO A = (A → CCS) → CCS

-- Monad combiantors
_>>=_ : ∀{A B} → FIO A → (A → FIO B) → FIO B
(¬¬a >>= a→¬¬b) b = ¬¬a λ a → a→¬¬b a b

pure : ∀{A} → A → FIO A
pure a = λ ¬a → ¬a a

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
lift-cmd _ ¬rc .tail rc = ¬rc rc

ccall : ∀ fun-sig → {{Call-Handle fun-sig}}
    → ⟦ arg-tys fun-sig ⟧as→
    FIO ⟦ ret-ty fun-sig ⟧r
ccall fs = convert-⟦⟧as λ as → lift-cmd (cmd 0 (cmd-ccall fs as))

return : ∀{R} → {{Ret-Handle R}} → ⟦ R ⟧r → FIO ⊥
return R _ .head = cmd 1 (cmd-return R)
return R _ .tail ()

-- Eliminator for FIO sugar layer
run : FIO ⊥ → CCS
run ¬¬⊥ = ¬¬⊥ λ ()




main : Exposed
main .own-signature = sig void "main" []
main .imported-sigs = put ∷ init ∷ dir ∷ sleep ∷ []
main .function-body = run do
    mapM' setup-pin (0 ∷ 1 ∷ 2 ∷ [])
    loop 0
  where
    setup-pin : Nat → FIO ⊤
    setup-pin n = do
        ccall init n
        ccall dir n true

    loop : Nat → FIO ⊥
    loop n _ .head = ccall' put n
    loop n k .tail c =
        ccall' sleep 200 >>=' λ _ →
        loop (n + 1) k
{-# COMPILE C main #-}
