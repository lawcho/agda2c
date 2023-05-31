
-- Print "Hej!\n" to stdout, then exit
module Examples.FFI.Hello where

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

hello : Exposed
hello .own-signature = sig void "main" []
hello .imported-sigs = put-u16 ∷ []
hello .function-body = do
    ccall put-u16 72
    ccall put-u16 101
    ccall put-u16 106
    ccall put-u16 33
    ccall put-u16 10
    () ← exit tt
{-# COMPILE C hello #-}
