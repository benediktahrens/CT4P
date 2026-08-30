{-# OPTIONS --rewriting #-}

-- Chapter 2: Brief Summary of Logical Foundations
module Foundations where

-- Sets/Collections:
module Collections where
  -- Agda features an infinite hierarchy of types |Set₀|, |Set₁|, |Set₂|, ...
  --
  -- We can also write |Set ℓ| where |ℓ : Level|.
  -- Levels support the following operations:
  -- > lzero : Level                 (zero)
  -- > lsuc  : Level → Level         (successor)
  -- > _⊔_   : Level → Level → Level (maximum)
  --
  -- Finally, |Set| is an alias for |Set₀|.
  --
  -- For more info, see 
  -- https://agda.readthedocs.io/en/stable/language/universe-levels.html
  open import Agda.Primitive using (Level; lzero; lsuc)
    renaming (_⊔_ to _lmax_) public

  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level

  module ExtraVars where
    variable
      X Y Z      : Set _
      x x₁ x₂ x₃ : X

      P : X → Set _
open Collections public

-- Functions:
module Functions where
  -- In Agda, we introduce functions with lambda abstractions (|λ x → ...|).
  --
  -- For more info, see 
  -- https://agda.readthedocs.io/en/stable/language/lambda-abstraction.html
  private module Example (ℕ ℚ : Set) (three : ℕ) (_/_ : ℕ → ℕ → ℚ) where
    _/3 : ℕ → ℚ
    _/3 = λ n → n / three

-- Cartesian Product
module Products where
  -- We define cartesian product as a specialisation of the more general sigma
  -- type.
  open import Agda.Builtin.Sigma public
  _×_ : Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ lmax ℓ₂)
  X × Y = Σ X λ _ → Y

  private module Example (ℕ : Set) (_+_ : ℕ → ℕ → ℕ) where
    add : ℕ × ℕ → ℕ
    add (n , m) = n + m

    add' : ℕ × ℕ → ℕ
    add' p = p .fst + p .snd
open Products public

-- Disjoint Union
module DisjointUnion where
  -- We define disjoint union with a dedicated inductive datatype.
  data _＋_ (X : Set ℓ₁) (Y : Set ℓ₂) : Set (ℓ₁ lmax ℓ₂) where
    inl : X → X ＋ Y
    inr : Y → X ＋ Y
open DisjointUnion public

-- Definitions
module Definitions where
  -- For more info, see 
  -- https://agda.readthedocs.io/en/stable/language/function-definitions.html
  private module Example (ℕ : Set) (_+_ : ℕ → ℕ → ℕ) where
    double : ℕ → ℕ
    double n = n + n

-- Equality
module Equality where
  -- We encode equality with Agda's built-in identity type, renamed to |_＝_|
  -- for consistency with the notes (note that |=| in Agda is reserved for
  -- definitions).
  open import Agda.Builtin.Equality renaming (_≡_ to _＝_) public

  open ExtraVars

  -- In a proof assistant, we often need to be more more explicit with equality
  -- than on paper. For example, manually applying symmetry (|sym|), 
  -- transitivity (|_∙_|) and congruence (|ap|).
  sym : x₁ ＝ x₂ → x₂ ＝ x₁
  sym refl = refl

  _∙_ : x₁ ＝ x₂ → x₂ ＝ x₃ → x₁ ＝ x₃
  refl ∙ q = q
  
  ap : (f : X → Y) → x₁ ＝ x₂ → f x₁ ＝ f x₂
  ap f refl = refl

  -- The raw combinators are not very readable, so sometimes we use equational
  -- reasoning syntax
  infixr 2 step-＝-⟩  step-＝-∣
  infix 3 _∎

  step-＝-⟩ : ∀ (x : X) {y z} → y ＝ z → x ＝ y → x ＝ z
  step-＝-⟩ x q p = p ∙ q

  step-＝-∣ : ∀ x {y : X} → x ＝ y → x ＝ y
  step-＝-∣ x p = p

  syntax step-＝-⟩ x q p = x ＝⟨ p ⟩ q
  syntax step-＝-∣ x p   = x ＝⟨⟩ p

  _∎ : ∀ (x : X) → x ＝ x
  x ∎ = refl

  -- Example:
  private
    example : ∀ {x y z} (f : X → Y) → x ＝ f y → y ＝ z → x ＝ f z
    example {x = x} {y = y} {z = z} f eq₁ eq₂ = 
      x
      ＝⟨ eq₁ ⟩
      f y
      ＝⟨ ap f eq₂ ⟩
      f z ∎

  -- We sometimes rely on function extensionality
  postulate
    funext : {Y : X → Set ℓ} {f g : (x : X) → Y x} → (∀ x → f x ＝ g x) → f ＝ g
  
open Equality public

-- Propositions and existence
module Prop where
  open ExtraVars
  
  -- In type theory, propositions are types with at most one element
  record IsProp (X : Set ℓ) : Set ℓ where
    field
      uniq : (x₁ x₂ : X) → x₁ ＝ x₂
  open IsProp public

  -- For example, the unit and empty types
  open import Agda.Builtin.Unit renaming (⊤ to 𝟙; tt to ⋆) public
  
  data 𝟘 : Set where
  
  -- Properties/predicates are families of propositions
  IsPred : {X : Set ℓ₁} (P : X → Set ℓ₂) → Set (ℓ₁ lmax ℓ₂)
  IsPred P = ∀ x → IsProp (P x)

  import Agda.Builtin.Equality.Rewrite

  -- In order to define existence as a proposition, we postulate "propositional 
  -- truncation" which squashes a type into the proposition of whether it is 
  -- inhabited
  postulate
    ∥_∥ : Set ℓ → Set ℓ 

    inh     : X → ∥ X ∥
    squash  : ∀ (x₁ x₂ : ∥ X ∥) → x₁ ＝ x₂
    ∥-∥rec  : IsProp Y → (X → Y) → ∥ X ∥ → Y
    rec-inh : {Yᴾ : IsProp Y} {f : X → Y} → ∥-∥rec Yᴾ f (inh x) ＝ f x
    {-# REWRITE rec-inh #-}

  NonEmpty = ∥_∥

  ∥-∥prop : IsProp ∥ X ∥
  ∥-∥prop .uniq = squash

  ∥-∥rec₂ : IsProp Z → (X → Y → Z) → ∥ X ∥ → ∥ Y ∥ → Z
  ∥-∥rec₂ Z-prop f x y 
    = ∥-∥rec Z-prop (λ x' → ∥-∥rec Z-prop (λ y' → f x' y') y) x

  ∥-∥map : (X → Y) → ∥ X ∥ → ∥ Y ∥
  ∥-∥map f x = ∥-∥rec ∥-∥prop (λ x' → inh (f x')) x

  ∥-∥map₂ : (X → Y → Z) → ∥ X ∥ → ∥ Y ∥ → ∥ Z ∥
  ∥-∥map₂ f x y 
    = ∥-∥rec₂ ∥-∥prop (λ x' y' → inh (f x' y')) x y

  -- Mere existence
  ∃ : (X : Set ℓ₁) → (X → Set ℓ₂) → Set (ℓ₁ lmax ℓ₂)
  ∃ X P = ∥ Σ X P ∥

  ∃-prop : IsProp (∃ X P)
  ∃-prop = ∥-∥prop 

  -- Unique existence
  record ∃! (X : Set ℓ₁) (P : X → Set ℓ₂) : Set (ℓ₁ lmax ℓ₂) where
    field
      exists  : X
      sat     : P exists
      uniq    : (x : X) (xᴾ : P x) → x ＝ exists

  data Dec (P : Set ℓ) : Set ℓ where
    yes : P → Dec P
    no  : (P → 𝟘) → Dec P

  LEM : (ℓ : Level) → Set (lsuc ℓ)
  LEM ℓ = (P : Set ℓ) → IsProp P → Dec P

open Prop public

-- More utilities
record Lift (X : Set ℓ₁) : Set (ℓ₁ lmax ℓ₂) where
  constructor lift
  field
    lower : X
open Lift public

open ExtraVars

Preimage : (X → Y) → Y → Set _
Preimage {X = X} f y = Σ X (λ □ → f □ ＝ y)

uip : IsProp (x₁ ＝ x₂)
uip .uniq refl refl = refl

open import Agda.Builtin.Bool public
open import Agda.Builtin.Nat hiding (_<_) public

infix 4 _＝[_]＝_
_＝[_]＝_ : X → X ＝ Y → Y → Set _
x ＝[ refl ]＝ y = x ＝ y
