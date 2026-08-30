{-# OPTIONS --rewriting #-}

open import Foundations
open ExtraVars using (X; Y; Z)

-- Chapter 3: Categories
module Categories where

-- Definition 1.
module Definition1 where
  record Category (ℓ₁ ℓ₂ : Level) : Set (lsuc (ℓ₁ lmax ℓ₂)) where
    field
      Ob  : Set ℓ₁
      Hom : Ob → Ob → Set ℓ₂

      id  : ∀ {x} → Hom x x
      _∘_ : ∀ {x y z} → Hom y z → Hom x y → Hom x z
      
      id∘ : ∀ {x y} (f : Hom x y) → id ∘ f ＝ f
      ∘id : ∀ {x y} (f : Hom x y) → f ∘ id ＝ f
      ∘∘  : ∀ {x y z w} (f : Hom x y) (g : Hom y z) (h : Hom z w)
          → h ∘ (g ∘ f) ＝ (h ∘ g) ∘ f
  open Category public
open Definition1 public

-- Example 4.
module Example4 where
  SET : Category _ _
  SET .Ob      = Set
  SET .Hom x y = x → y

  SET .id  x     = x
  SET ._∘_ g f x = g (f x)
  -- Lemma 5.
  SET .id∘ f     = refl
  SET .∘id f     = refl
  SET .∘∘  f g h = refl

-- We mechanise example 8 and exercise 9 later (DCPOs are a little complicated)

-- Example 10.
module Example10 where
  -- Preordered sets
  record Preorder (ℓ₁ ℓ₂ : Level) : Set (lsuc (ℓ₁ lmax ℓ₂)) where
    field
      Car : Set ℓ₁
      _≤_ : Car → Car → Set ℓ₂

      ≤-prop : ∀ {x y : Car} → IsProp (x ≤ y)

      refl≤  : ∀ {x : Car} → x ≤ x
      trans≤ : ∀ {x y z : Car} → x ≤ y → y ≤ z → x ≤ z

  module _ (X : Preorder ℓ₁ ℓ₂) (let module X = Preorder X) where
    -- Every preordered set can be turned into a category
    Pre2Cat : Category _ _
    Pre2Cat .Ob        = X.Car
    Pre2Cat .Hom x y   = x X.≤ y
    Pre2Cat .id        = X.refl≤
    Pre2Cat ._∘_ q p   = X.trans≤ p q
    Pre2Cat .id∘ f     = X.≤-prop .uniq _ _
    Pre2Cat .∘id f     = X.≤-prop .uniq _ _
    Pre2Cat .∘∘  f g h = X.≤-prop .uniq _ _

-- Exercise 12.
module Exercise12 where
  open Example10 

  -- Partially ordered sets
  record Poset (ℓ₁ ℓ₂ : Level) : Set (lsuc (ℓ₁ lmax ℓ₂))  where
    field
      Car : Set ℓ₁
      _≤_ : Car → Car → Set ℓ₂

      ≤-prop : ∀ {x y} → IsProp (x ≤ y)

      refl≤    : ∀ {x} → x ≤ x
      trans≤   : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
      antisym≤ : ∀ {x y} → x ≤ y → y ≤ x → x ＝ y

    -- Every partially ordered set is a preorder
    Pre : Preorder ℓ₁ ℓ₂
    Pre = record { Car = Car; _≤_ = _≤_; ≤-prop = ≤-prop 
                 ; refl≤ = refl≤ ; trans≤ = trans≤ }

  module _ (𝒫 : Poset ℓ₁ ℓ₂) (let module 𝒫 = Poset 𝒫) where
    Pos2Cat : Category ℓ₁ ℓ₂
    Pos2Cat = Pre2Cat 𝒫.Pre

    private module Pos2Cat = Category Pos2Cat

    -- Given a loop containing |x| and |y|, we can show |x| and |y| are
    -- actually the same object.
    trivial-loops : ∀ {x y} → (f : Pos2Cat.Hom x y) (g : Pos2Cat.Hom y x)
                  → x ＝ y
    trivial-loops f g = 𝒫.antisym≤ f g

-- Example 14.
module Example14 where
  open Exercise12
  open Poset

  variable
    o n m l k : Nat

  _∣_ : Nat → Nat → Set
  n ∣ m = NonEmpty (Preimage (m *_) n)

  -- We need a few of basic properties of addition/multiplication
  +-ass : (n + m) + l ＝ n + (m + l)
  +-ass {n = zero}  = refl
  +-ass {n = suc n} = ap suc (+-ass {n = n})

  *one : n * 1 ＝ n
  *one {n = zero}  = refl
  *one {n = suc n} = ap suc *one

  +*-distr : (n + m) * l ＝ n * l + m * l
  +*-distr {n = zero}  = refl
  +*-distr {n = suc n} {m = m} {l = l} = 
    l + (n + m) * l
    ＝⟨ ap (l +_) (+*-distr {n = n}) ⟩
    l + (n * l + m * l)
    ＝⟨ sym (+-ass {n = l}) ⟩
    l + n * l + m * l ∎

  *-ass : (n * m) * l ＝ n * (m * l)
  *-ass {n = zero}  = refl
  *-ass {n = suc n} {m = m} {l = l} = 
    (m + n * m) * l
    ＝⟨ +*-distr {n = m} ⟩
    m * l + (n * m) * l
    ＝⟨ ap ((m * l) +_) (*-ass {n = n}) ⟩
    m * l + n * (m * l) ∎

  refl-∣ : n ∣ n
  refl-∣ = inh (1 , *one)

  trans-∣ : n ∣ m → m ∣ l → n ∣ l
  trans-∣ {l = l} 
    = ∥-∥map₂ λ where (k , refl) (o , refl) → o * k , sym (*-ass {n = l})

  -- TODO
  -- Probably easiest to go via antisymmetry of numerical ordering
  antisym-∣ : n ∣ m → m ∣ n → n ＝ m
  antisym-∣ = {!!}

  ∣-Pos : Poset _ _
  ∣-Pos .Car     = Nat
  ∣-Pos ._≤_ n m = n ∣ m

  ∣-Pos .≤-prop = ∥-∥prop
  ∣-Pos .refl≤  = refl-∣
  ∣-Pos .trans≤ {z = z} div₁ div₂ 
    = trans-∣ {l = z} div₁ div₂
  ∣-Pos .antisym≤ div₁ div₂ 
    = antisym-∣ div₁ div₂

  ∣-Cat : Category _ _
  ∣-Cat = Pos2Cat ∣-Pos

-- Example 15.
module Example15 where
  open Exercise12
  open Poset

  variable
    b : Bool

  data _≤𝔹_ : Bool → Bool → Set where
    f≤t    : false ≤𝔹 true
    refl≤𝔹 : b ≤𝔹 b

  𝔹-Pos : Poset _ _
  𝔹-Pos .Car = Bool
  𝔹-Pos ._≤_ = _≤𝔹_

  𝔹-Pos .≤-prop .uniq f≤t    f≤t    = refl
  𝔹-Pos .≤-prop .uniq refl≤𝔹 refl≤𝔹 = refl

  𝔹-Pos .refl≤    = refl≤𝔹
  𝔹-Pos .trans≤ f≤t    refl≤𝔹 = f≤t
  𝔹-Pos .trans≤ refl≤𝔹 leq₂   = leq₂
  
  𝔹-Pos .antisym≤ f≤t ()
  𝔹-Pos .antisym≤ refl≤𝔹 refl≤𝔹 = refl


module Example16 where
  open Exercise12

  module _ (𝒫₁ 𝒫₂ : Poset ℓ₁ ℓ₂) 
           (let module 𝒫₁ = Poset 𝒫₁) (let module 𝒫₂ = Poset 𝒫₂) where
    -- Monotone maps between partially ordered sets
    -- (Poset morphisms)
    record MonotoneMap : Set (ℓ₁ lmax ℓ₂) where
      field
        act    : 𝒫₁.Car → 𝒫₂.Car
        pres-≤ : ∀ {x y} → x 𝒫₁.≤ y → act x 𝒫₂.≤ act y
  open MonotoneMap

  -- Category of partially ordered sets
  POS : Category _ _
  POS .Ob  = Poset lzero lzero
  POS .Hom = MonotoneMap

  POS .id         .act    x   = x
  POS .id {x = 𝒫} .pres-≤ leq = leq
    where module 𝒫 = Poset 𝒫
  POS ._∘_ f g .act    x   = f .act (g .act x)
  POS ._∘_ {x = 𝒫₁} {y = 𝒫₂} {z = 𝒫₃} f g .pres-≤ leq 
    = f .pres-≤ (g .pres-≤ leq)
    where module 𝒫₁ = Poset 𝒫₁
          module 𝒫₂ = Poset 𝒫₂
          module 𝒫₃ = Poset 𝒫₃

  POS .id∘ f     = refl
  POS .∘id f     = refl
  POS .∘∘  f g h = refl

-- Lemma 17.
module Lemma17 (𝒞 : Category ℓ₁ ℓ₂) (let module 𝒞 = Category 𝒞) where
  -- Property of being an identity morphism
  IsId : ∀ {x} (id' : 𝒞.Hom x x) → Set (ℓ₁ lmax ℓ₂)
  IsId {x = x} id' = ∀ {y} (f : 𝒞.Hom x y) → f 𝒞.∘ id' ＝ f

  id-uniq : ∀ {x} (id' : 𝒞.Hom x x) → IsId id' → id' ＝ 𝒞.id
  id-uniq id' id'-id = 
    id'
    ＝⟨ sym (𝒞.id∘ id') ⟩
    𝒞.id 𝒞.∘ id'
    ＝⟨ id'-id 𝒞.id ⟩
    𝒞.id ∎

-- Example 18. TODO

-- Definition 19.
module Definition19 where
  -- Monoids
  record Monoid (ℓ : Level) : Set (lsuc ℓ) where
    field
      Car  : Set ℓ
      _◆_  : Car → Car → Car
      id   : Car

      id◆ : ∀ x → id ◆ x ＝ x
      ◆id : ∀ x → x ◆ id ＝ x
      ◆◆  : ∀ x y z → (x ◆ y) ◆ z ＝ x ◆ (y ◆ z)

  module _ (M : Monoid ℓ) (let module M = Monoid M) where    
    Mon2Cat : Category lzero ℓ
    Mon2Cat .Ob      = 𝟙
    Mon2Cat .Hom ⋆ ⋆ = M.Car
    
    Mon2Cat .id      = M.id
    Mon2Cat ._∘_ y x = x M.◆ y

    Mon2Cat .id∘      = M.◆id
    Mon2Cat .∘id      = M.id◆
    Mon2Cat .∘∘ x y z = M.◆◆ x y z
open Definition19 public

-- Remark 20.
module Remark20 (I : Set ℓ₁) (M : Monoid ℓ₂) (let module M = Monoid M) where
  Mon2Cat' : Category ℓ₁ (ℓ₁ lmax ℓ₂)
  Mon2Cat' .Ob      = I
  Mon2Cat' .Hom i j = (i ＝ j) × M.Car
  
  Mon2Cat' .id  = refl , M.id
  Mon2Cat' ._∘_ (refl , y) (refl , x) = refl ,  x M.◆ y
  
  Mon2Cat' .id∘ (refl , x) 
    = ap (_ ,_) (M.◆id x)
  Mon2Cat' .∘id (refl , x) 
    = ap (_ ,_) (M.id◆ x)
  Mon2Cat' .∘∘  (refl , x) (refl , y) (refl , z) 
    = ap (_ ,_) (M.◆◆ x y z)

-- Exercise 21.
module Exercise21 (𝒞 : Category lzero ℓ₂) (let module 𝒞 = Category 𝒞) where
  open Monoid 

  module _ (x : 𝒞.Ob) (x-uniq : ∀ {y} → x ＝ y) where
    Mon2Cat⁻¹ : Monoid ℓ₂
    Mon2Cat⁻¹ .Car = 𝒞.Hom x x

    Mon2Cat⁻¹ ._◆_ f g = g 𝒞.∘ f
    Mon2Cat⁻¹ .id      = 𝒞.id

    Mon2Cat⁻¹ .id◆ f     = 𝒞.∘id f
    Mon2Cat⁻¹ .◆id f     = 𝒞.id∘ f
    Mon2Cat⁻¹ .◆◆  f g h = 𝒞.∘∘ f g h

  -- To prove 𝒞 is actually "of the form" (i.e. equivalent to) 
  -- |Mon2Cat Mon2Cat⁻¹|, we need to have a proper characterisation of 
  -- equivalence of categories.

module Exercise22 where
  module _ (M₁ M₂ : Monoid ℓ)
           (let module M₁ = Monoid M₁) (let module M₂ = Monoid M₂)
           where
    -- Monoid homomorphisms
    record MonoidHom : Set ℓ where
      field
        act     : M₁.Car → M₂.Car
        pres-◆  : ∀ {x y} → act (x M₁.◆ y) ＝ act x M₂.◆ act y
        pres-id : act M₁.id ＝ M₂.id
    
  module _ {M₁ M₂ : Monoid ℓ}
           {f g : MonoidHom M₁ M₂}
           (let module f = MonoidHom f) (let module g = MonoidHom g)
           where
    -- TODO (depends on |funext|)
    monoidHom＝ : (∀ x → f.act x ＝ g.act x) → f ＝ g
    monoidHom＝ = {!!}
  open MonoidHom

  -- Category of monoids
  MON : Category _ _
  MON .Ob  = Monoid lzero
  MON .Hom = MonoidHom
  MON .id .act x   = x
  MON .id .pres-◆  = refl
  MON .id .pres-id = refl
  MON ._∘_ g f .act x   = g .act (f . act x)
  MON ._∘_ {x = M₁} {y = M₂} {z = M₃} g f .pres-◆ {x = x} {y = y} = 
    g .act (f .act (x M₁.◆ y))
    ＝⟨ ap (g .act) (f .pres-◆) ⟩
    g .act (f .act x M₂.◆ f .act y)
    ＝⟨ g .pres-◆ ⟩
    g .act (f .act x) M₃.◆ g .act (f .act y) ∎ where
      module M₁ = Monoid M₁
      module M₂ = Monoid M₂
      module M₃ = Monoid M₃
  MON ._∘_ {x = M₁} {y = M₂} {z = M₃} g f .pres-id =
    g .act (f .act M₁.id)
    ＝⟨ ap (g .act) (f .pres-id) ⟩
    g .act M₂.id
    ＝⟨ g .pres-id ⟩
    M₃.id ∎ where
      module M₁ = Monoid M₁
      module M₂ = Monoid M₂
      module M₃ = Monoid M₃
  MON .id∘ f     = monoidHom＝ λ _ → refl
  MON .∘id f     = monoidHom＝ λ _ → refl
  MON .∘∘  f g h = monoidHom＝ λ _ → refl

module Exercise23 (𝒞 : Category ℓ₁ ℓ₂) (let module 𝒞 = Category 𝒞) where
  -- Opposite categories
  _ᴼᴾ : Category ℓ₁ ℓ₂
  _ᴼᴾ .Ob      = 𝒞.Ob
  _ᴼᴾ .Hom x y = 𝒞.Hom y x

  _ᴼᴾ .id      = 𝒞.id
  _ᴼᴾ ._∘_ g f = f 𝒞.∘ g

  _ᴼᴾ .id∘ f     = 𝒞.∘id f
  _ᴼᴾ .∘id f     = 𝒞.id∘ f
  _ᴼᴾ .∘∘  f g h = sym (𝒞.∘∘ h g f)

-- Example 8.
module Example8 where
  open Exercise12
  open Example16

  -- In type theory, we can encode subsets (of |X|) via power sets 
  -- (|X → Set ℓ|) or families (|Σ (Set ℓ) (λ I → X)|).
  -- The family approach works out much more nicely when defining
  -- continuous maps between DCPOs (where we need to map the subset
  -- over the action - see 'mapFam')
  record Fam (X : Set ℓ₁) (ℓ₂ : Level) : Set (ℓ₁ lmax lsuc ℓ₂) where
    field
      Idx : Set ℓ₂
      fam : Idx → X

  module _ where
    open Fam
    mapFam : (X → Y) → Fam X ℓ₂ → Fam Y ℓ₂
    mapFam f ℱ .Idx   = ℱ .Idx
    mapFam f ℱ .fam i = f (ℱ .fam i)

  module _ (𝒫 : Poset ℓ₁ ℓ₂) (let module 𝒫 = Poset 𝒫) where
    -- Binary upper bounds
    record IsUB2 (x y z : 𝒫.Car) : Set ℓ₂ where
      field
        left≤  : x 𝒫.≤ z
        right≤ : y 𝒫.≤ z

    -- Directed subsets (encoded as directed families)
    record DirSubset (ℓ₃ : Level) : Set (ℓ₁ lmax ℓ₂ lmax lsuc ℓ₃) where
      field
        Idx : Set ℓ₃
        fam : Idx → 𝒫.Car
      
      Family : Fam 𝒫.Car _
      Family = record {Idx = Idx; fam = fam}

      field
        has-upper : (i j : Idx) 
                  → ∃ Idx λ k → IsUB2 (fam i) (fam j) (fam k)

        nonempty : NonEmpty Idx
    open DirSubset public

    module _ (ℱ : Fam 𝒫.Car ℓ₃) (let module ℱ = Fam ℱ) where
      -- Family upper bounds
      IsUB∞ : 𝒫.Car → Set (ℓ₂ lmax ℓ₃)
      IsUB∞ x = (i : ℱ.Idx) → ℱ.fam i 𝒫.≤ x

      -- Family least upper bounds
      record IsLUB∞ (x : 𝒫.Car) : Set (ℓ₁ lmax ℓ₂ lmax ℓ₃) where
        field
          upper : IsUB∞ x
          least : ∀ y → IsUB∞ y → x 𝒫.≤ y

  module _ {𝒫₁ 𝒫₂ : Poset ℓ₁ ℓ₂} (f : MonotoneMap 𝒫₁ 𝒫₂) where
    open MonotoneMap
    open IsUB2

    mapIsUB2 : ∀ {x y z} 
            → IsUB2 𝒫₁ x y z → IsUB2 𝒫₂ (f .act x) (f .act y) (f .act z)
    mapIsUB2 ub .left≤  = f .pres-≤ (ub .left≤)
    mapIsUB2 ub .right≤ = f .pres-≤ (ub .right≤)

    mapDirSubset : DirSubset 𝒫₁ ℓ₃ → DirSubset 𝒫₂ ℓ₃
    mapDirSubset D .Idx   = D .Idx
    mapDirSubset D .fam i = f .act (D .fam i)
    mapDirSubset D .has-upper i j 
      = ∥-∥map (λ (i , ub) → i , mapIsUB2 ub) (D .has-upper i j)
    mapDirSubset D .nonempty      
      = D .nonempty

  -- Pointed direct complete partial orders
  record Dcpo (ℓ₁ ℓ₂ ℓ₃ : Level) : Set (lsuc (ℓ₁ lmax ℓ₂ lmax ℓ₃))  where
    field
      Car : Set ℓ₁
      _≤_ : Car → Car → Set ℓ₂

      ≤-prop : ∀ {x y} → IsProp (x ≤ y)

      refl≤    : ∀ {x} → x ≤ x
      trans≤   : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
      antisym≤ : ∀ {x y} → x ≤ y → y ≤ x → x ＝ y

    Pos : Poset ℓ₁ ℓ₂
    Pos = record { Car = Car ; _≤_ = _≤_ ; ≤-prop = ≤-prop 
                 ; refl≤ = refl≤ ; trans≤ = trans≤ ; antisym≤ = antisym≤ }
    private module Pos = Poset Pos
    
    field
      ⨆    : DirSubset Pos ℓ₃ → Pos.Car
      ⨆ᴸᵁᴮ : (D : DirSubset Pos ℓ₃) → IsLUB∞ Pos (Family D) (⨆ D) 
      ⊥    : Pos.Car
      ⊥≤   : ∀ {x} → ⊥ Pos.≤ x

  open Poset
  open Dcpo

-- Exercise 9.
module Exercise9 where
  open Example8
  open Example16

  module _ (𝒟₁ 𝒟₂ : Dcpo ℓ₁ ℓ₂ ℓ₃) 
           (let module 𝒟₁ = Dcpo 𝒟₁) (let module 𝒟₂ = Dcpo 𝒟₂) where
    open IsLUB∞
    open IsUB2
    open Fam

    -- Strictly continuous maps between DCPOs
    record ContMap : Set (ℓ₁ lmax ℓ₂ lmax lsuc ℓ₃) where
      field
        act    : 𝒟₁.Car → 𝒟₂.Car
        pres-⨆ : (D : DirSubset 𝒟₁.Pos ℓ₃) {x : 𝒟₁.Car}
               → IsLUB∞ 𝒟₁.Pos (Family D) x
               → IsLUB∞ 𝒟₂.Pos (mapFam act (Family D)) (act x) 
        pres-⊥ : act 𝒟₁.⊥ ＝ 𝒟₂.⊥

      -- Every strictly continuous map is monotone
      pres-≤ : ∀ {x y} → x 𝒟₁.≤ y → act x 𝒟₂.≤ act y
      pres-≤ {x = x} {y = y} leq = go .upper (lift true) where 
        xy : Fam 𝒟₁.Car _
        xy .Idx = Lift Bool
        xy .fam (lift true)  = x
        xy .fam (lift false) = y

        y-ub : (i j : Bool) 
             → IsUB2 𝒟₁.Pos (fam xy (lift i)) (fam xy (lift j)) y
        y-ub false j .left≤  = 𝒟₁.refl≤
        y-ub true  j .left≤  = leq
        y-ub i false .right≤ = 𝒟₁.refl≤
        y-ub i true  .right≤ = leq

        xyᴰ : DirSubset (𝒟₁.Pos) ℓ₃
        xyᴰ .Idx           = xy .Idx
        xyᴰ .fam           = xy .fam
        xyᴰ .has-upper i j = inh (lift false , y-ub (i .lower) (j .lower))
        xyᴰ .nonempty      = inh (lift true)

        y-lub : IsLUB∞ 𝒟₁.Pos (Family xyᴰ) y
        y-lub .upper (lift true)  = leq
        y-lub .upper (lift false) = 𝒟₁.refl≤
        y-lub .least z ub = ub (lift false)

        go : IsLUB∞ 𝒟₂.Pos (mapFam act xy) (act y)
        go = pres-⨆ xyᴰ y-lub

      mono : MonotoneMap 𝒟₁.Pos 𝒟₂.Pos
      mono = record { act = act; pres-≤ = pres-≤ }

  module _ {𝒟₁ 𝒟₂ : Dcpo ℓ₁ ℓ₂ ℓ₃} {f g : ContMap 𝒟₁ 𝒟₂}
           (let module f = ContMap f) (let module g = ContMap g) where
    -- TODO (depends on |funext|)
    contMap＝ : (∀ x → f.act x ＝ g.act x) → f ＝ g
    contMap＝ = {!!}

  open ContMap

  DCPO : Category _ _
  DCPO .Ob        = Dcpo lzero lzero lzero
  DCPO .Hom 𝒟₁ 𝒟₂ = ContMap 𝒟₁ 𝒟₂
  DCPO .id          .act x        = x
  DCPO .id {x = 𝒟₁} .pres-⨆ D lub = lub
    where module 𝒟₁ = Dcpo 𝒟₁
  DCPO .id .pres-⊥ = refl
  DCPO ._∘_ {x = 𝒟₁} {y = 𝒟₂} {z = 𝒟₃} f g .act x = f.act (g.act x)
    where module f = ContMap f
          module g = ContMap g
  DCPO ._∘_ {x = 𝒟₁} {y = 𝒟₂} {z = 𝒟₃} f g .pres-⨆ D lub
    = f.pres-⨆ (mapDirSubset g.mono D) (g.pres-⨆ D lub) 
    where module f = ContMap f
          module g = ContMap g
  DCPO ._∘_ {x = 𝒟₁} {y = 𝒟₂} {z = 𝒟₃} f g .pres-⊥ = 
    f.act (g.act 𝒟₁.⊥)
    ＝⟨ ap f.act g.pres-⊥ ⟩
    f.act 𝒟₂.⊥
    ＝⟨ f.pres-⊥ ⟩
    𝒟₃.⊥ ∎ where 
      module f = ContMap f
      module g = ContMap g
      module 𝒟₁ = Dcpo 𝒟₁
      module 𝒟₂ = Dcpo 𝒟₂
      module 𝒟₃ = Dcpo 𝒟₃
  DCPO .id∘ f     = contMap＝ λ _ → refl
  DCPO .∘id f     = contMap＝ λ _ → refl
  DCPO .∘∘  f g h = contMap＝ λ _ → refl

  Hask = DCPO
