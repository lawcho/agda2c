-- Example from Koen's PMC paper

{-# OPTIONS --guardedness #-}
module Examples.FFI.Cat-Fish where
open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.Nat
open import Examples.Lib.PMC
open import Examples.Lib.ITree


-- Portable (monadic) Agda code


-- Hack to work around agda2c's lack of String & Char support (13 Jun '23)
Char = Nat
String = List Char   -- since Strings & Chars sare currently unsupported in the agda2c backend (13 Jun '23)
start! = 115 ∷ 116 ∷ 97 ∷ 114 ∷ 116 ∷ 33 ∷ []
cat = 99 ∷ 97 ∷ 116 ∷ []
fish = 102 ∷ 105 ∷ 115 ∷ 104 ∷ []


-- Writer monad's write function
write' : String → ITree⁺ (Writer Nat) ⊤
write' [] = pure tt
write' (c ∷ s) .head = inr c    -- write c
write' (c ∷ s) .tail _ = write' s

-- PMC monad's write function (atomic)
write : String → Thread (Writer Nat) ⊤
write s = lift do
    write' s
    pure (pure tt)

example : Thread (Writer Nat) ⊤
example = do
    write start!
    fork (loop (write fish))
    loop (write cat)
    pure tt

-- FFI glue

open import Foreign-C.Core
open import Foreign-C.FFI-Compiler
open Exposed

c-import = "
#include<stdio.h>
#include<inttypes.h>
void put_u16(uint16_t x){
    printf(\"%c\",(char)x);
    fflush(stdout);
}
void nop(void){return;}
"
{-# COMPILE RAW_C c-import #-}

put-u16 = sig void "put_u16" (uint16 ∷ [])
nop = sig void "nop" []

main : Exposed
main .own-signature = sig void "main" []
main .imported-sigs = put-u16 ∷ nop ∷ []
main .function-body = run-Thread
    ((λ n → cmd 0 (cmd-ccall put-u16 (n , tt))) , λ _ → tt)
    example
{-# COMPILE C main #-}
