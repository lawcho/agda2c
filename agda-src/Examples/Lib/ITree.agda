{-# OPTIONS --guardedness #-}

-- Theory of (lawless) Interaction Trees
-- reference: https://dl.acm.org/doi/10.1145/3371119
module Examples.Lib.ITree where

-- Definitons
module _ where

    -- Effects packaging inspired by Niek Mulleners' paper:
    -- https://studenttheses.uu.nl/handle/20.500.12932/37758
    record Sig : Set₁ where
        constructor _▹_
        field Cmd : Set
        field Ret : Cmd → Set
    _▸_ = λ c r → c ▹ λ _ → r

    -- (Infinite) Interaction Trees
    record ITree (E : Sig) : Set where
        coinductive
        open Sig E
        field head : Cmd
        field tail : Ret head → ITree E
    open ITree public

-- Standard FP utils
module _ where
    data _⊎_ (A B : Set) : Set where
        inl : A → A ⊎ B
        inr : B → A ⊎ B 

    data ⊥ : Set where  -- empty type

    open import Agda.Builtin.Equality public

    -- Dependent function composition
    _∘_ : ∀{ℓa}{ℓb}{ℓc}{A : Set ℓa}{B : A → Set ℓb}{C : ∀{a} → B a → Set ℓc}
        → (f : ∀{a} → (b : B a) → C b)
        → (g : (a : A) → B a)
        → (a : A) → C (g a)
    (f ∘ g) a = f (g a)
    infixr 20 _∘_

    -- Identity function
    id : ∀{ℓa}{A : Set ℓa} → A → A
    id a = a

    -- aka transport
    _∵_ : ∀{ℓ}{A B : Set ℓ} → A → A ≡ B → B
    a ∵ refl = a
    infix 15 _∵_

    -- aka cong
    _under_ : ∀{ℓa ℓb}{A : Set ℓa}{B : Set ℓb}{x y : A}
        → x ≡ y
        → (f : A → B)
        → f x ≡ f y
    refl under _ = refl

    -- aka sym
    flip : ∀{ℓa}{A : Set ℓa}{x y : A}
        → x ≡ y → y ≡ x
    flip refl = refl

-- Misc. combinators
module _ where
    open Sig

    -- Combine Ret functions.
    -- (Simplified version of Niek Mulleners' _▿_ combinator)
    _▿_ : {C₁ C₂ : Set}
        → (R₁ : C₁ → Set)
        → (R₂ : C₂ → Set)
        → (C₁ ⊎ C₂) → Set
    (f ▿ _) (inl x) = f x
    (_ ▿ g) (inr y) = g y

    -- Combine effects. (from Niek Mulleners' MSc report)
    _⊕_ : Sig → Sig → Sig
    (C₁ ▹ R₁) ⊕ (C₂ ▹ R₂) = (C₁ ⊎ C₂) ▹ (R₁ ▿ R₂)
    infixr 20 _⊕_

    -- Effect transformations
    -- (specialised version of Niek Mulleners' _⇒_ combinator)
    record _⇒_ (E₁ E₂ : Sig) : Set where
        constructor _,_
        field cmap : Cmd E₁ → Cmd E₂
        field rmap : ∀{c} → Ret E₂ (cmap c) → Ret E₁ c
    open _⇒_
    infixr 4 _,_ -- matches Agda.Builtin.Sigma.Σ._,_ to avoid parse issues

    -- Trivial effect transformation
    id-⇒ : ∀{E} → E ⇒ E
    id-⇒ = id , id

    -- Composition of effect transformations
    _∘-⇒_ : ∀{E₁ E₂ E₃} → (E₁ ⇒ E₂) → (E₂ ⇒ E₃) → (E₁ ⇒ E₃)
    (cmap₁₂ , rmap₂₁) ∘-⇒ (cmap₂₃ , rmap₃₂) = (cmap₂₃ ∘ cmap₁₂) , (rmap₂₁ ∘ rmap₃₂)
    infixr 20 _∘-⇒_

    -- Interaction of _⇒_ and _⊕_
    _⇒⊕_ : ∀{E₁ E₂ E'} → (E₁ ⇒ E') → (E₂ ⇒ E') → (E₁ ⊕ E₂) ⇒ E'
    (cmap₁ , rmap₁) ⇒⊕ (cmap₂ , rmap₂)
        = (λ where (inl e₁c) → cmap₁ e₁c ; (inr e₂c) → cmap₂ e₂c)
        , λ where {inl _} e'r → rmap₁ e'r ; {inr _} e'r → rmap₂ e'r
    infixr 20 _⇒⊕_

    _⇒⊕'_ : ∀{E₁ E₂ E₁' E₂'} → (E₁ ⇒ E₁') → (E₂ ⇒ E₂') → (E₁ ⊕ E₂) ⇒ (E₁' ⊕ E₂')
    (cmap₁ , rmap₁) ⇒⊕' (cmap₂ , rmap₂) = (inl ∘ cmap₁ , rmap₁) ⇒⊕ (inr ∘ cmap₂ , rmap₂)
    infixr 20 _⇒⊕'_

    -- Effect transformations can be weakened on the left and right
    weakenₗ-⇒ : ∀{E' E₁ E₂} → E₁ ⇒ E₂ → (E' ⊕ E₁) ⇒ (E' ⊕ E₂)
    weakenₗ-⇒ = id-⇒ ⇒⊕'_

    weakenᵣ-⇒ : ∀{E' E₁ E₂} → E₁ ⇒ E₂ → (E₁ ⊕ E') ⇒ (E₂ ⊕ E')
    weakenᵣ-⇒ = _⇒⊕' id-⇒

    -- Effects can be weakened on the left and right
    weakenₗ-⊕ : ∀{E' E} → E ⇒ (E' ⊕ E)
    weakenₗ-⊕ = inr , id

    weakenᵣ-⊕ : ∀{E' E} → E ⇒ (E ⊕ E')
    weakenᵣ-⊕ = inl , id

    -- Identical effects can be combined
    join-⊕ : ∀{E} → (E ⊕ E) ⇒ E
    join-⊕
        =   (λ where (inl ec) → ec ; (inr ec) → ec)
        ,   λ where {inl _} er → er ; {inr _} er → er

    -- Apply an ITree transformation
    tmap : ∀{E₁ E₂} → (E₁ ⇒ E₂) → ITree E₁ → ITree E₂
    tmap (cmap , rmap) t₁ .head = cmap (t₁ .head)
    tmap (cmap , rmap) t₁ .tail r₂ = tmap (cmap , rmap) (t₁ .tail (rmap r₂))

    -- ITrees can be wekened on the left and right
    weakenₗ-ITree : ∀{E E'} → ITree E → ITree (E' ⊕ E)
    weakenₗ-ITree = tmap weakenₗ-⊕

    weakenᵣ-ITree : ∀{E' E} → ITree E → ITree (E ⊕ E')
    weakenᵣ-ITree = tmap weakenᵣ-⊕

-- The 'stop and return a value of type A' effect
module _  where

    Pure : Set → Sig
    Pure A = A ▸ ⊥

    -- The effect can be eliminated by providing a function that consumes all generated output values
    elim-Pure : ∀{A E} → (A → ITree E) → ITree (Pure A ⊕ E) → ITree E
    elim-Pure f t with t .head in pf
    ... | inl a = f a
    ... | inr c = λ where
        .head → c
        .tail r → elim-Pure f (t .tail (r ∵ flip pf under (_ ▿ _)))

    -- The Pure effect adds a type parameter to an ITree
    ITree⁺ : Sig → Set → Set
    ITree⁺ E A = ITree (Pure A ⊕ E)

    -- Monad-like combinators for ITree⁺
    fmap : ∀{E A B} → (A → B) → ITree⁺ E A → ITree⁺ E B
    fmap f = tmap (weakenᵣ-⇒ (f , id))

    join : ∀{E A} → ITree⁺ E (ITree⁺ E A) → ITree⁺ E A
    join tta with tta .head in pf
    ... | inl ta = ta
    ... | inr ec = λ where
        .head → inr ec
        .tail er → join (tta .tail (er ∵ (flip pf under (_ ▿ _))))
    
    _>>=_ : ∀{E A B} → ITree⁺ E A → (A → ITree⁺ E B) → ITree⁺ E B
    ta >>= a→tb = join (fmap a→tb ta)

    _>>_ : ∀{E A B} → ITree⁺ E A → ITree⁺ E B → ITree⁺ E B
    ta >> tb = ta >>= λ _ → tb

    pure : ∀ {E A} → A → ITree⁺ E A
    pure a .head = inl a
    pure a .tail ()

    -- Add an unused effect to an ITree⁺
    weakenₗ-ITree⁺ : ∀{E E' A} → ITree⁺ E A → ITree⁺ (E' ⊕ E) A
    weakenₗ-ITree⁺ = tmap (weakenₗ-⇒ weakenₗ-⊕)

-- The 'no-op' effect
module _ where
    open import Agda.Builtin.Unit

    Nop : Sig
    Nop = ⊤ ▸ ⊤

    -- Nops can be eliminated by translating them to other effects
    elim-Nop : ∀{E} → E .Sig.Cmd → ITree (Nop ⊕ E) → ITree E
    elim-Nop c = tmap
        (   (λ where (inl tt) → c; (inr c') → c')
        ,   λ where {inl _} _ → tt; {inr _} z → z)

-- The Writer effect
module _ where
    open import Agda.Builtin.Unit

    Writer : Set → Sig
    Writer A = A ▸ ⊤

-- Translation to/from Foreign-C types
module _ where
    open import Foreign-C.Core

    FFI-Effect = Cmd ▹ cmd-ret-ty

    itree→ccs : ITree FFI-Effect → CCS
    itree→ccs t .CCS.head = t .ITree.head
    itree→ccs t .CCS.tail r = itree→ccs (t .ITree.tail r)

    ccs→itree : CCS → ITree FFI-Effect
    ccs→itree s .head = s .CCS.head
    ccs→itree s .tail r = ccs→itree (s .CCS.tail r)
