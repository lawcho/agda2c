
-- https://wokwi.com/projects/343960210261410387

open import Foreign-C.Sugared

imp = "#include<pico/stdlib.h>"
{-# COMPILE RAW_C imp #-}

put = sig void "gpio_put_all" (uint16 ∷ [])
init = sig void "gpio_init" (uint16 ∷ [])
dir = sig void "gpio_set_dir" (uint16 ∷ bool ∷ [])
sleep = sig void "sleep_ms" (uint16 ∷ [])

main : Exposed
main .own-signature = sig void "main" []
main .imported-sigs = put ∷ init ∷ dir ∷ sleep ∷ []
main .function-body = do
    ccall init 8
    ccall dir  8 true
    ccall init 7
    ccall dir  7 true
    ccall init 6
    ccall dir  6 true
    ccall init 5
    ccall dir  5 true
    ccall init 4
    ccall dir  4 true
    ccall init 3
    ccall dir  3 true
    ccall init 2
    ccall dir  2 true
    ccall init 1
    ccall dir  1 true
    ccall init 0
    ccall dir  0 true
    loop 0
  where
    loop : Nat → CCS
    loop n .head = ccall put n
    loop n .tail c = do
        ccall sleep 200
        loop (n + 1)
{-# COMPILE C main #-}
