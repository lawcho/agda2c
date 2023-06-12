
-- More advanced example, using several helpers 
module Examples.FFI.Apa-Hund where

open import Agda.Builtin.List
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

open import Examples.FFI.FIO-Lib

c-import = "
#include<stdio.h>
#include<inttypes.h>
void put_u16(uint16_t x){
    printf(\"%c\",(char)x);
    fflush(stdout);
}"
{-# COMPILE RAW_C c-import #-}

put-u16-sig = sig void "put_u16" (uint16 ∷ [])

-- Hand-unpacked strings to work around unimplemented Strings in backend (18 May '23)
apa = 65 ∷ 112 ∷ 97 ∷ 10 ∷ []
hund = 72 ∷ 117 ∷ 110 ∷ 100 ∷ 10 ∷ []

-- Helper functions that depend on put_u16
module _ {{_ : Call-Handle put-u16-sig}} where

    put-chars : List Nat → FIO ⊤
    put-chars = mapM' (ccall put-u16-sig)

monkey-dog : Exposed
monkey-dog .own-signature = sig void "main" []
monkey-dog .imported-sigs = put-u16-sig ∷ []
monkey-dog .function-body = run do
    put-chars apa
    put-chars hund
    return tt
    put-chars apa
    return tt
{-# COMPILE C monkey-dog #-}
