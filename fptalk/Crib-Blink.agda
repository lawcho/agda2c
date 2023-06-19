
open import Foreign-C.Sugared

imp = "#include<pico/stdlib.h>"
{-# COMPILE RAW_C imp #-}

init = sig void "gpio_init" (uint16 ∷ [])
dir = sig void "gpio_set_dir" (uint16 ∷ bool ∷ [])
put = sig void "gpio_put" (uint16 ∷ bool ∷ [])
sleep = sig void "sleep_ms" (uint16 ∷ [])

main : Exposed
main .own-signature = sig void "main" []
main .imported-sigs = put ∷ init ∷ sleep ∷ dir ∷ []
main .function-body = do
    ccall init 25
    ccall dir 25 true
    loop
  where
    loop : CCS
    loop .head = ccall put 25 true
    loop .tail _ = do
        ccall sleep 300
        ccall put 25 false
        ccall sleep 500
        loop
{-# COMPILE C main #-}
