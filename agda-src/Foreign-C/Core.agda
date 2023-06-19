

-- Agda/C foreign function interface

-- Defintions in this module are designed for
-- compiler- and runtime- (rather than human-) friendliness

{-# OPTIONS -W noNoGuardednessFlag #-}
module Foreign-C.Core where

open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat;suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Unit using (⊤;tt)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Sigma using (Σ;_,_)
open import Agda.Builtin.List using (List;[];_∷_)

-----------------------------------
-- Standard functional utilities --
-----------------------------------

data ⊥ : Set where -- empty type

-- Map a function over a list
map : ∀{ℓa ℓb}{A : Set ℓa} {B : Set ℓb} → (A → B) → List A → List B
map _ [] = []
map f (a ∷ as) = f a ∷ map f as

-- Non-dependent pair type
_×_ : Set → Set → Set
A × B = Σ A λ _ → B

-- Hetrogenous n-ary functions
_⋯→_ : List Set → Set → Set
[] ⋯→ B = B
(A ∷ As) ⋯→  B = A → As ⋯→  B
infixr 20 _⋯→_

-- Hetrogenous n-ary instance-arg functions
_⋯⦃⦄→_ : List Set → Set → Set
[] ⋯⦃⦄→ B = B
(A ∷ As) ⋯⦃⦄→  B = {{ A }} → As ⋯⦃⦄→  B
infixr 20 _⋯⦃⦄→_

---------------------------------------
-- The type system of C (simplified) --
---------------------------------------

-- Return types
data Ret-Type : Set where
    void : Ret-Type
    uint16 bool : Ret-Type

-- Argument types
data Arg-Type : Set where
    uint16 bool : Arg-Type

-- C function signatures
record Sig : Set where
    constructor sig
    field ret-ty    : Ret-Type
    field name      : String
    field arg-tys   : List Arg-Type
open Sig

-------------------------------
-- Relating C and Agda types --
-------------------------------

-- Mapping C types to Agda types
⟦_⟧r : Ret-Type → Set
⟦ uint16 ⟧r = Nat
⟦ bool ⟧r = Bool
⟦ void ⟧r = ⊤

⟦_⟧a : Arg-Type → Set
⟦ uint16 ⟧a = Nat
⟦ bool ⟧a = Bool

-- Agda arguments to foregin function calls
⟦_⟧as : List Arg-Type → Set
⟦ [] ⟧as = ⊤
⟦ at ∷ ats ⟧as = ⟦ at ⟧a × ⟦ ats ⟧as

-------------------------------------------
-- User interface to the run-time engine --
-------------------------------------------

-- Design note (Lawrence Dec'22)
--  * This library uses the 'abstract handle' design pattern (aka 'capabilities')
--      to enforce various safety properties.
--  * Advantages over the obvious alternative (lots of type indices) include:
--      * Fewer parameters to functions (keeps the run-time engine simple)
--      * Simpler types (keeps the library human-friendly)
abstract
    -- At type-checking time, enforces the "all foreign functions must be known at compile time" restriction
    -- At run-time, carries a number used to decide which function to call.
    Call-Handle : Sig → Set
    Call-Handle _ = ⟦ uint16 ⟧r

    -- At type-checking time, enforces the "functions always return the correct type" restriction
    -- At run-time, carries no information.
    Ret-Handle : Ret-Type → Set
    Ret-Handle _ = ⊤

-- Design note (Lawrence Dec'22):
--  I am deliberately avoiding 'data' types
--  in favour of explicit Nat-tagged unions,
--  since these are more easily inspected by an imperative run-time engine
--  i.e. to decode a command, the run-time engine only ever needs
--  to apply functions and split on 'Nat' s

-- The 'ccall' command calls a foreign C function
record Cmd-ccall : Set where
    constructor cmd-ccall
    field fun-sig : Sig
    field {{fun-handle}} : Call-Handle fun-sig
    field fun-args : ⟦ arg-tys fun-sig ⟧as

-- The 'return' command exits the current function
record Cmd-return : Set where
    constructor cmd-return
    field {ret-type} : Ret-Type
    field {{ret-handle}} : Ret-Handle ret-type
    field ret-value : ⟦ ret-type ⟧r

-- Mapping numeric op-codes to command types
cmd-arg-ty : Nat → Set
cmd-arg-ty 0 = Cmd-ccall
cmd-arg-ty _ = Cmd-return

record Cmd : Set where
    constructor cmd
    field op-code : ⟦ uint16 ⟧r
    field cmd-arg : cmd-arg-ty op-code

-- What is the return type of each command?
cmd-ret-ty : Cmd → Set
cmd-ret-ty (cmd 0 (cmd-ccall s _)) = ⟦ ret-ty s ⟧r
cmd-ret-ty (cmd (suc _) (cmd-return _ )) = ⊥

-- Coinductive Command Stream.
-- aka "Interaction Tree", "Coinductive Free Monad"
record CCS : Set where
    coinductive
    constructor _>>=_   -- CCS is not a monad (no argument, head has the wrong type)
    field head : Cmd
    field tail : cmd-ret-ty head → CCS

-- Type of Agda→C function exports
record Exposed : Set where field
    own-signature : Sig               -- C function signature to export the function to
    imported-sigs : List Sig          -- function signatures of C dependencies
    function-body :
        -- The body is given instance-findable handles for...
        {{Ret-Handle (ret-ty own-signature)}} → -- returning a value
        map Call-Handle imported-sigs ⋯⦃⦄→     -- calling its (pre-declared) FFs
        map ⟦_⟧a (arg-tys own-signature) ⋯→  -- the body is passed its arguments (from C)
        CCS                                 -- the body then produces a stream

------------------------------------------------------
-- Functions used internally by the run-time engine --
------------------------------------------------------

-- Convert a marshallable Agda value to a C-friendly Nat
to-Nat : ∀{t} → ⟦ t ⟧r → Nat
to-Nat {uint16} n = n
to-Nat {bool} false = 0
to-Nat {bool} true = 1
to-Nat {void} _ = 0

-- Convert a Nat to an Agda value at any marshallable type
from-Nat : ∀{t} → Nat → ⟦ t ⟧r
from-Nat {uint16} n = n
from-Nat {bool} 0 = false
from-Nat {bool} _ = true
from-Nat {void} _ = tt

-- Design note (Lawrence Dec'22)
--  Implementing these functions in Agda helps modularise the run-time engine implementation.
--  In partialuar, the FFI implementation does not need to know about the encoding of data types,
--  i.e. it only needs to inspect/construct 'Nat' s, and apply Agda functons
