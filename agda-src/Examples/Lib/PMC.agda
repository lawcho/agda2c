{-# OPTIONS --guardedness #-}

-- Port of Koen Claessen's Poor Man's Concurrency Monad,
-- (https://dl.acm.org/doi/10.1017/S0956796899003342)
-- presented as an Interaction-Tree effect
module Examples.Lib.PMC where

open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.List

open import Examples.Lib.ITree

-- Get Haskell-like syntax to emulate Koen's paper
private variable
    m : Sig
    α : Set

-- Type defintions

-- Design note (Lawrence Jun '23):
-- Koen presents the PMC monad as a hand-rolled monad transformer.
-- I couldn't get this to termination-check in Agda, so I refactored it
-- into a (coinductive, container-extension based) algebraic effect

-- The Fork effect. Forking returns a bit indicating which child this is.
Fork = ⊤ ▸ Bool

-- The Stop effect. Terminates a thread, so the return type is very loose.
Stop = ⊤ ▸ ⊥

-- The Yield effect. Allows another thread to run.
-- Not in Koen's paper, but used here to implement atomicity.
Yield = ⊤ ▸ ⊤

-- Stream of PMC commands (called 'C' in Koen's paper)
Thread : Sig → Set → Set
Thread m α = ITree⁺ (Fork ⊕ Stop ⊕ Yield ⊕ {- Atom -} m) α

-- Helper functions for constructing Thread s
-- (from Koen's paper)


stop : Thread m α
stop .head = inr (inr (inl tt))
stop .tail ()

par : Thread m α → Thread m α → Thread m α
par m₁ m₂ .head = inr (inl tt)  -- ask the interpreter to split the thread and pass a bool to each fragment
par m₁ m₂ .tail false = m₁          -- the 'true' fragment runs m₁
par m₁ m₂ .tail true = m₂           -- the 'false' fragment runs m₂

fork : Thread m α → Thread m ⊤
fork m .head = inr (inl tt) -- ask the interpreter to split the thread and pass a bool to each fragment
fork m .tail false = pure tt        -- the 'true' fragment (the 'parent') does nothing
fork m .tail true = m >> pure tt    -- the 'false' fragment (the 'child') runs m and discards its result

yield : Thread m ⊤
yield .head = inr (inr (inl tt))
yield .tail ()

atom : ITree⁺ m (Thread m α) → Thread m α
atom t = let
    flattened =
        elim-Pure id
        -- t : ITree⁺                                 m  (Thread m α)
        -- ↓ : ITree⁺ (Pure α ⊕ Fork ⊕ Stop ⊕ Yield ⊕ m) (Thread m α)
        (weakenₗ-ITree⁺ (weakenₗ-ITree⁺ (weakenₗ-ITree⁺ (weakenₗ-ITree⁺ t))))
    in do
        -- begin critical section
        a ← flattened   -- the scheduler will run each of these commands individually, but without switching to other threads
        yield -- end critical section
        pure a

lift = atom

-- Extra combinator to help writing loops
-- Equivalent to (loop t = t >> loop t), but passes productivity checking
loop : Thread m ⊤ → Thread m ⊥
loop {m} t₀ = go t₀ where
    go : Thread m ⊤ → Thread m ⊥
    go t with t .head in pf
    ... | (inl tt) {- pure -} = λ where
        .head → inr (inr (inr (inl (tt)))) -- yeild (guarantees productivity)
        .tail _ → loop t₀   -- restart from the beginning
    ... | inr c {- any other command -} = λ where
        .head → inr c
        .tail r → go (t .tail (r ∵ flip pf under (_ ▿ _)))

-- PMC Interpreter

-- List snoc function. Naive implementation
_⍮⍮_ : ∀{ℓ}{A : Set ℓ} → List A → A → List A
[] ⍮⍮ a = a ∷ []
(x ∷ l1) ⍮⍮ a = x ∷ (l1 ⍮⍮ a)
infixl 20 _⍮⍮_

-- Round robin scheduler
-- The Nop effect is allows the interpreter to procrastinate indefinetely
-- when evalaluating programs (e.g. when evaluating a fork bomb)
round : List (Thread m ⊤) → ITree⁺ (Nop ⊕ m) ⊤
round [] = pure tt
round (t ∷ ts) with t .head in pf
... | inl tt       {- pure -} = round ts
... | inr (inl tt) {- fork -} = λ where
        .head → inr (inl tt) -- nop
        .tail tt → round (ts
            ⍮⍮ t .tail (false ∵ flip pf under (_ ▿ _))
            ⍮⍮ t .tail (true ∵ flip pf under (_ ▿ _)))
... | inr (inr (inl tt)) {- stop -} = round ts
... | inr (inr (inr (inl x))) {- yield -} = λ where
        .head → inr (inl tt) -- nop
        .tail r → round (ts ⍮⍮ t .tail (r ∵ flip pf under (_ ▿ _)))
... | inr (inr (inr (inr c))) {- atom -} = λ where
        .head → inr (inr c)
        -- Put the continutaiton at the *front* of the buffer,
        -- to ensure atomicity (the atom will be termianted by a yield)
        .tail r → round (t .tail (r ∵ flip pf under (_ ▿ _)) ∷ ts)

-- Run a PMC computation in a CCS
open import Foreign-C.Core
run-Thread : (m ⇒ FFI-Effect)
    → Thread m ⊤
    → {{Call-Handle (sig void "nop" [])}} → {{Ret-Handle void}} → CCS
run-Thread {m} f t₀ = let
    -- (1) Eliminate concurrency via round-robin scheduling
    t₁ : ITree⁺ (Nop ⊕ m) ⊤
    t₁ = round (t₀ ∷ [])
    -- (2) Eliminate Pure ⊤, Nop, and m by transforming them into FFI-Effect s
    t₂ : ITree FFI-Effect
    t₂ = tmap ((cmd 1 ∘ cmd-return , λ ())  -- map Pure ⊤ to C return
            ⇒⊕ (cmd 0 ∘ cmd-ccall _ , id)   -- map Nop to C call of nop function
            ⇒⊕ f                            -- eliminate m using f
            ) t₁
    -- (3) Convert to CCS
    in itree→ccs t₂
 