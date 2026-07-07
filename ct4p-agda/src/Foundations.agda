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
  open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public

  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level

  module ExtraVars where
    variable
      X Y Z      : Set _
      x x₁ x₂ x₃ : X
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
  _×_ : Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
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
  data _+_ (X : Set ℓ₁) (Y : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    inl : X → X + Y
    inr : Y → X + Y
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

  -- We assume function extensionality where necessary.
  Funext : (X : Set ℓ₁) → (X → Set ℓ₂) → Set _
  Funext X Y = {f g : (x : X) → Y x} → ((x : X) → f x ＝ g x) → f ＝ g

  -- TODO: Propositions and "exists uniquely"
  -- Do we want to use |Prop|, truncation, hProp, or something else?
open Equality public
