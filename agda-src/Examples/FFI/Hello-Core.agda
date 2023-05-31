
-- Print "Hej!\n" to stdout, then exit
module Examples.FFI.Hello-Core where

open import Agda.Builtin.List
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

open import Foreign-C.Core
open Exposed
open CCS
open Cmd
open Cmd-ccall

c-import = "
#include<stdio.h>
#include<inttypes.h>
void put_u16(uint16_t x){
    printf(\"%c\",(char)x);
    fflush(stdout);
}"
{-# COMPILE RAW_C c-import #-}

hello : Exposed
hello .own-signature = sig void "main" []
hello .imported-sigs = (sig void "put_u16" (uint16 ∷ [])) ∷ []

hello .function-body {{ret-handle}} {{put-u16-handle}} =
    cmd 0 (cmd-ccall _ {{put-u16-handle}} (72 , tt)) >>= λ _ →
    cmd 0 (cmd-ccall _ {{put-u16-handle}} (101 , tt)) >>= λ _ →
    cmd 0 (cmd-ccall _ {{put-u16-handle}} (106 , tt)) >>= λ _ →
    cmd 0 (cmd-ccall _ {{put-u16-handle}} (33 , tt)) >>= λ _ →
    cmd 0 (cmd-ccall _ {{put-u16-handle}} (10 , tt)) >>= λ _ →
    cmd 1 (cmd-return {void} {{ret-handle}} tt) >>= λ ()
{-# COMPILE C hello #-}
 