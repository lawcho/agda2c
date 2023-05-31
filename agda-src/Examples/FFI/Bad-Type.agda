
-- Write a 1,2,3,4 to stdout, then exit
module Examples.FFI.Bad-Type where

open import Agda.Builtin.String


str = "Hello World"
{-# COMPILE C str #-}

open import Foreign-C.FFI-Compiler
