{-# OPTIONS --guardedness #-}


-- Print "Hej!\n" to stdout, in a loop forever
module Examples.FFI.Hello-Loop where

open import Foreign-C.Sugared

c-import = "
#include<stdio.h>
#include<inttypes.h>
void put_u16(uint16_t x){
    printf(\"%c\",(char)x);
    fflush(stdout);
}"
{-# COMPILE RAW_C c-import #-}

put-u16 = sig void "put_u16" (uint16 ∷ [])


loop : {{Call-Handle put-u16}} → CCS
loop .head = ccall put-u16 0
loop .tail _ = do
    ccall put-u16 72
    ccall put-u16 101
    ccall put-u16 106
    ccall put-u16 33
    ccall put-u16 10
    loop

hello : Exposed
hello .own-signature = sig void "main" []
hello .imported-sigs = put-u16 ∷ []
hello .function-body = loop
{-# COMPILE C hello #-}
 