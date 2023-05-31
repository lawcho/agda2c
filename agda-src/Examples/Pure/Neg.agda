-- {-# OPTIONS --erasure #-}

-- Examples with advanced case-splitting on simple data types
module Examples.Pure.Neg where

-- Simple case: no type parameters, no constructor args
module Simple where
    data Bool : Set where
        true false : Bool

    neg : Bool → Bool
    neg true = false
    neg nalse = true

-- With ignored module parameter
module ModPar (A : Set) where
    data Bool : Set where
        true false : Bool

    neg : Bool → Bool
    neg true = false
    neg false = true

-- With ignored data type parameter
module DatPar where
    data Bool (A : Set) : Set where
        true false : Bool A

    neg : ∀{A} → Bool A → Bool A
    neg true = false
    neg false = true

-- With data type index, refined by constructors
module DatIdx where
    data Bool : Simple.Bool → Set where
        true : Bool Simple.true
        false : Bool Simple.false

    neg : ∀{b} → Bool b → Bool (Simple.neg b)
    neg true = false
    neg false = true

-- With data type index, constructor argument
module DatIdx+ConArg where
    data Bool : Set → Set where
        true false : ∀{A} → Bool A

    neg : ∀{A} → Bool A → Bool A
    neg true = false
    neg false = true

-- With data type index, erased constructor argument
module DatIdx+EraConArg where
    data Bool : Set → Set where
        true false : ∀{@0 A} → Bool A

    neg : ∀{A} → Bool A → Bool A
    neg true = false
    neg false = true

-- With erased data type index, erased constructor argument
module EraDatIdx+EraConArg where
    data Bool : @0 Set → Set where
        true false : ∀{@0 A} → Bool A

    neg : ∀{A} → Bool A → Bool A
    neg true = false
    neg false = true
 