
open import Foreign-C.Sugared

imp = "#include<stdio.h>"
{-# COMPILE RAW_C imp #-}

put = sig void "putchar" (uint16 ∷ [])

main : Exposed
main .own-signature = sig void "main" []
main .imported-sigs = put ∷ []
main .function-body = loop where
    loop : CCS
    loop .head = ccall put 72
    loop .tail _ = do
        ccall put 101
        ccall put 108
        ccall put 108
        ccall put 111
        ccall put 32
        ccall put 87
        ccall put 111
        ccall put 114
        ccall put 108
        ccall put 100
        ccall put 33
        ccall put 10
        loop
{-# COMPILE C main #-}
