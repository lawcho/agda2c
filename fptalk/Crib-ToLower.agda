
open import Foreign-C.Sugared

imp = "#include<stdio.h>"
{-# COMPILE RAW_C imp #-}

put = sig void "putchar" (uint16 ∷ [])
get = sig uint16 "getchar" []

main : Exposed
main .own-signature = sig void "main" []
main .imported-sigs = put ∷ get ∷ []
main .function-body = loop where
    loop : CCS
    loop .head = ccall get
    loop .tail c = do
        ccall put (c + 32)
        loop
{-# COMPILE C main #-}
