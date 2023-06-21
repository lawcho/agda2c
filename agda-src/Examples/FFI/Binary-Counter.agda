
-- Count in binary on LEDs attached to the RPP's pins
-- Simulator at https://wokwi.com/projects/343960210261410387

module Examples.FFI.Binary-Counter where
open import Examples.Lib.FIO

imp = "#include<pico/stdlib.h>"
{-# COMPILE RAW_C imp #-}

put = sig void "gpio_put_all" (uint16 ∷ [])
init = sig void "gpio_init" (uint16 ∷ [])
dir = sig void "gpio_set_dir" (uint16 ∷ bool ∷ [])
sleep = sig void "sleep_ms" (uint16 ∷ [])

main : Exposed
main .own-signature = sig void "main" []
main .imported-sigs = put ∷ init ∷ dir ∷ sleep ∷ []
main .function-body = run do
    mapM' setup-pin (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
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
