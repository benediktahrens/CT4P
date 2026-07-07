open import Foundations

-- Chapter 3: Categories
module Categories where

  -- Definition 1.
record Category (ℓ₁ ℓ₂ : Level) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    Ob  : Set ℓ₁
    Hom : Ob → Ob → Set ℓ₂

    id  : ∀ {x} → Hom x x
    _∘_ : ∀ {x y z} → Hom y z → Hom x y → Hom x z
    
    id∘ : ∀ {x y} {f : Hom x y} → id ∘ f ＝ f
    ∘id : ∀ {x y} {f : Hom x y} → f ∘ id ＝ f
    ∘∘  : ∀ {x y z w} {f : Hom x y} {g : Hom y z} {h : Hom z w}
        → h ∘ (g ∘ f) ＝ (h ∘ g) ∘ f
open Category public

-- Example 3.
SET : Category _ _
SET .Ob      = Set
SET .Hom x y = x → y

SET .id  x     = x
SET ._∘_ g f x = g (f x)
-- Lemma 4.
SET .id∘ = refl
SET .∘id = refl
SET .∘∘  = refl

-- TODO: Can we simulate the |Hask| example with pointed types?

-- Example 10.
record Preorder (ℓ₁ ℓ₂ : Level) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    Car : Set ℓ₁
    _≤_ : Car → Car → Set ℓ₂

    -- TODO: How do we want to handle propositions?
    ≤-prop : ∀ {x y : Car} {p q : x ≤ y} → p ＝ q

    refl≤  : ∀ {x : Car} → x ≤ x
    trans≤ : ∀ {x y z : Car} → x ≤ y → y ≤ z → x ≤ z

module _ (X : Preorder ℓ₁ ℓ₂) where
  module X = Preorder X

  Pre2Cat : Category ℓ₁ ℓ₂
  Pre2Cat .Ob      = X.Car
  Pre2Cat .Hom x y = x X.≤ y
  Pre2Cat .id      = X.refl≤
  Pre2Cat ._∘_ q p = X.trans≤ p q
  Pre2Cat .id∘     = X.≤-prop
  Pre2Cat .∘id     = X.≤-prop
  Pre2Cat .∘∘      = X.≤-prop
