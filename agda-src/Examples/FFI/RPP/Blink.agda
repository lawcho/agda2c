
{-# OPTIONS --guardedness #-}

-- Blink the RPP LED at 1s period, forever
module Examples.FFI.RPP.Blink where

led-pin = 25
delay = 500

open import Foreign-C.Sugared

c-import = "
#include<pico/stdlib.h>
"
{-# COMPILE RAW_C c-import #-}


gpio-init = sig void "gpio_init" (uint16 ∷ [])
gpio-set-dir = sig void "gpio_set_dir" (uint16 ∷ bool ∷ [])
gpio-put = sig void "gpio_put" (uint16 ∷ bool ∷ [])
sleep-ms = sig void "sleep_ms" (uint16 ∷ [])

loop : {{Call-Handle gpio-put}} → {{Call-Handle sleep-ms}} → CCS
loop .head = ccall gpio-put led-pin true
loop .tail _ = do
    ccall sleep-ms delay
    ccall gpio-put led-pin false
    ccall sleep-ms delay
    loop

blink : Exposed
blink .own-signature = sig void "main" []
blink .imported-sigs = gpio-init ∷ gpio-set-dir ∷ gpio-put ∷ sleep-ms ∷ []
blink .function-body = do
    ccall gpio-init led-pin
    ccall gpio-set-dir led-pin true -- set LED pin to 'output' mode
    loop
{-# COMPILE C blink #-}
