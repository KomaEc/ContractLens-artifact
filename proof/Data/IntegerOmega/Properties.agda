

module Data.IntegerOmega.Properties where

open import Data.IntegerOmega.Base

open import Level using (0ℓ)

open import Data.Bool using (Bool; true; false)
open import Data.Sum using (inj₁; inj₂; map)

import Data.Nat as Nat
import Data.Integer as Int
import Data.Integer.Properties
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Sign as Sign using () renaming (_*_ to _𝕊*_)
import Data.Sign.Properties as 𝕊ₚ
open import Data.Unit using (tt)
open import Function.Base using (_∘_; _$_; id)
open import Data.Empty using (⊥; ⊥-elim)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; trans; sym; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; map′)
open import Relation.Binary
open import Relation.Binary.Structures
open import Relation.Binary.Bundles

open import Algebra.Bundles
import Algebra.Morphism as Morphism
open import Algebra.Construct.NaturalChoice.Base
import Algebra.Construct.NaturalChoice.MinMaxOp as MinMaxOp

open import Algebra.Definitions {A = ℤω} _≡_
open import Algebra.Consequences.Propositional
open import Algebra.Structures {A = ℤω} _≡_


-- ≤ properties
≤-reflexive : _≡_ ⇒ _≤_
≤-reflexive { -∞ }  refl = -∞≤any
≤-reflexive {fin x} refl = fin≤fin (Data.Integer.Properties.≤-reflexive refl)

≤-trans : Transitive _≤_
≤-trans -∞≤any      _           = -∞≤any
≤-trans (fin≤fin R) (fin≤fin S) = fin≤fin (Data.Integer.Properties.≤-trans R S)

≤-total : Total _≤_
≤-total -∞      y       = inj₁ -∞≤any
≤-total x       -∞      = inj₂ -∞≤any
≤-total (fin x) (fin y) = map fin≤fin fin≤fin (Data.Integer.Properties.≤-total x y)

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ -∞<any = -∞≤any
<⇒≤ (fin<fin prf) = fin≤fin (Data.Integer.Properties.<⇒≤ prf)

≰⇒> : _≰_ ⇒ _>_
≰⇒> { -∞} {_} i≰j = ⊥-elim (i≰j -∞≤any)
≰⇒> {fin _} { -∞} i≰j = -∞<any
≰⇒> {fin i} {fin j} i≰j = fin<fin (Data.Integer.Properties.≰⇒> (λ z → i≰j (fin≤fin z)))



-- Structures
≤-isPreorder : IsPreorder _≡_ _≤_
≤-isPreorder = record
  { isEquivalence = Eq.isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

≤-isTotalPreorder : IsTotalPreorder _≡_ _≤_
≤-isTotalPreorder = record
  { isPreorder = ≤-isPreorder
  ; total      = ≤-total
  }

≤-totalPreorder : TotalPreorder 0ℓ 0ℓ 0ℓ
≤-totalPreorder = record { isTotalPreorder = ≤-isTotalPreorder }


-- min max properties
i≤j⇒i⊓j≡i : ∀ {x y} → x ≤ y → x ⊓ y ≡ x
i≤j⇒i⊓j≡i { -∞ }  {_}     -∞≤any      = refl
i≤j⇒i⊓j≡i {fin x} {fin y} (fin≤fin R) = cong fin (Data.Integer.Properties.i≤j⇒i⊓j≡i R)

i≥j⇒i⊓j≡j : ∀ {x y} → x ≥ y → x ⊓ y ≡ y
i≥j⇒i⊓j≡j { -∞ }  { -∞ }  -∞≤any      = refl
i≥j⇒i⊓j≡j {fin _} { -∞ }  -∞≤any      = refl
i≥j⇒i⊓j≡j {fin x} {fin y} (fin≤fin R) = cong fin (Data.Integer.Properties.i≥j⇒i⊓j≡j R)

i≤j⇒i⊔j≡j : ∀ {x y} → x ≤ y → x ⊔ y ≡ y
i≤j⇒i⊔j≡j { -∞ }  {_}     -∞≤any      = refl
i≤j⇒i⊔j≡j {fin x} {fin y} (fin≤fin R) = cong fin (Data.Integer.Properties.i≤j⇒i⊔j≡j R)

i≥j⇒i⊔j≡i : ∀ {x y} → x ≥ y → x ⊔ y ≡ x
i≥j⇒i⊔j≡i { -∞ }  { -∞ }  -∞≤any      = refl
i≥j⇒i⊔j≡i {fin _} { -∞ }  -∞≤any      = refl
i≥j⇒i⊔j≡i {fin x} {fin y} (fin≤fin R) = cong fin (Data.Integer.Properties.i≥j⇒i⊔j≡i R)


⊓-operator : MinOperator ≤-totalPreorder
⊓-operator = record
  { x≤y⇒x⊓y≈x = i≤j⇒i⊓j≡i
  ; x≥y⇒x⊓y≈y = i≥j⇒i⊓j≡j
  }

⊔-operator : MaxOperator ≤-totalPreorder
⊔-operator = record
  { x≤y⇒x⊔y≈y = i≤j⇒i⊔j≡j
  ; x≥y⇒x⊔y≈x = i≥j⇒i⊔j≡i
  }

-- Automatically derived properties of _⊓_ and _⊔_

private
  module ⊓-⊔-properties = MinMaxOp ⊓-operator ⊔-operator

open ⊓-⊔-properties public
  using
  ( ⊓-idem                    -- : Idempotent _⊓_
  ; ⊓-sel                     -- : Selective _⊓_
  ; ⊓-assoc                   -- : Associative _⊓_
  ; ⊓-comm                    -- : Commutative _⊓_

  ; ⊔-idem                    -- : Idempotent _⊔_
  ; ⊔-sel                     -- : Selective _⊔_
  ; ⊔-assoc                   -- : Associative _⊔_
  ; ⊔-comm                    -- : Commutative _⊔_

  ; ⊓-distribˡ-⊔              -- : _⊓_ DistributesOverˡ _⊔_
  ; ⊓-distribʳ-⊔              -- : _⊓_ DistributesOverʳ _⊔_
  ; ⊓-distrib-⊔               -- : _⊓_ DistributesOver  _⊔_
  ; ⊔-distribˡ-⊓              -- : _⊔_ DistributesOverˡ _⊓_
  ; ⊔-distribʳ-⊓              -- : _⊔_ DistributesOverʳ _⊓_
  ; ⊔-distrib-⊓               -- : _⊔_ DistributesOver  _⊓_
  ; ⊓-absorbs-⊔               -- : _⊓_ Absorbs _⊔_
  ; ⊔-absorbs-⊓               -- : _⊔_ Absorbs _⊓_
  ; ⊔-⊓-absorptive            -- : Absorptive _⊔_ _⊓_
  ; ⊓-⊔-absorptive            -- : Absorptive _⊓_ _⊔_

  ; ⊓-isMagma                 -- : IsMagma _⊓_
  ; ⊓-isSemigroup             -- : IsSemigroup _⊓_
  ; ⊓-isCommutativeSemigroup  -- : IsCommutativeSemigroup _⊓_
  ; ⊓-isBand                  -- : IsBand _⊓_
  ; ⊓-isSemilattice           -- : IsSemilattice _⊓_
  ; ⊓-isSelectiveMagma        -- : IsSelectiveMagma _⊓_

  ; ⊔-isMagma                 -- : IsMagma _⊔_
  ; ⊔-isSemigroup             -- : IsSemigroup _⊔_
  ; ⊔-isCommutativeSemigroup  -- : IsCommutativeSemigroup _⊔_
  ; ⊔-isBand                  -- : IsBand _⊔_
  ; ⊔-isSemilattice           -- : IsSemilattice _⊔_
  ; ⊔-isSelectiveMagma        -- : IsSelectiveMagma _⊔_

  ; ⊔-⊓-isLattice             -- : IsLattice _⊔_ _⊓_
  ; ⊓-⊔-isLattice             -- : IsLattice _⊓_ _⊔_
  ; ⊔-⊓-isDistributiveLattice -- : IsDistributiveLattice _⊔_ _⊓_
  ; ⊓-⊔-isDistributiveLattice -- : IsDistributiveLattice _⊓_ _⊔_

  ; ⊓-magma                   -- : Magma _ _
  ; ⊓-semigroup               -- : Semigroup _ _
  ; ⊓-band                    -- : Band _ _
  ; ⊓-commutativeSemigroup    -- : CommutativeSemigroup _ _
  ; ⊓-semilattice             -- : Semilattice _ _
  ; ⊓-selectiveMagma          -- : SelectiveMagma _ _

  ; ⊔-magma                   -- : Magma _ _
  ; ⊔-semigroup               -- : Semigroup _ _
  ; ⊔-band                    -- : Band _ _
  ; ⊔-commutativeSemigroup    -- : CommutativeSemigroup _ _
  ; ⊔-semilattice             -- : Semilattice _ _
  ; ⊔-selectiveMagma          -- : SelectiveMagma _ _

  ; ⊔-⊓-lattice               -- : Lattice _ _
  ; ⊓-⊔-lattice               -- : Lattice _ _
  ; ⊔-⊓-distributiveLattice   -- : DistributiveLattice _ _
  ; ⊓-⊔-distributiveLattice   -- : DistributiveLattice _ _

  ; ⊓-glb                     -- : ∀ {m n o} → m ≥ o → n ≥ o → m ⊓ n ≥ o
  ; ⊓-triangulate             -- : ∀ m n o → m ⊓ n ⊓ o ≡ (m ⊓ n) ⊓ (n ⊓ o)
  ; ⊓-mono-≤                  -- : _⊓_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ; ⊓-monoˡ-≤                 -- : ∀ n → (_⊓ n) Preserves _≤_ ⟶ _≤_
  ; ⊓-monoʳ-≤                 -- : ∀ n → (n ⊓_) Preserves _≤_ ⟶ _≤_

  ; ⊔-lub                     -- : ∀ {m n o} → m ≤ o → n ≤ o → m ⊔ n ≤ o
  ; ⊔-triangulate             -- : ∀ m n o → m ⊔ n ⊔ o ≡ (m ⊔ n) ⊔ (n ⊔ o)
  ; ⊔-mono-≤                  -- : _⊔_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ; ⊔-monoˡ-≤                 -- : ∀ n → (_⊔ n) Preserves _≤_ ⟶ _≤_
  ; ⊔-monoʳ-≤                 -- : ∀ n → (n ⊔_) Preserves _≤_ ⟶ _≤_
  )
  renaming
  ( x⊓y≈y⇒y≤x to i⊓j≡j⇒j≤i    -- : ∀ {i j} → i ⊓ j ≡ j → j ≤ i
  ; x⊓y≈x⇒x≤y to i⊓j≡i⇒i≤j    -- : ∀ {i j} → i ⊓ j ≡ i → i ≤ j
  ; x⊓y≤x     to i⊓j≤i        -- : ∀ i j → i ⊓ j ≤ i
  ; x⊓y≤y     to i⊓j≤j        -- : ∀ i j → i ⊓ j ≤ j
  ; x≤y⇒x⊓z≤y to i≤j⇒i⊓k≤j    -- : ∀ {i j} k → i ≤ j → i ⊓ k ≤ j
  ; x≤y⇒z⊓x≤y to i≤j⇒k⊓i≤j    -- : ∀ {i j} k → i ≤ j → k ⊓ i ≤ j
  ; x≤y⊓z⇒x≤y to i≤j⊓k⇒i≤j    -- : ∀ {i} j k → i ≤ j ⊓ k → i ≤ j
  ; x≤y⊓z⇒x≤z to i≤j⊓k⇒i≤k    -- : ∀ {i} j k → i ≤ j ⊓ k → i ≤ k

  ; x⊔y≈y⇒x≤y to i⊔j≡j⇒i≤j    -- : ∀ {i j} → i ⊔ j ≡ j → i ≤ j
  ; x⊔y≈x⇒y≤x to i⊔j≡i⇒j≤i    -- : ∀ {i j} → i ⊔ j ≡ i → j ≤ i
  ; x≤x⊔y     to i≤i⊔j        -- : ∀ i j → i ≤ i ⊔ j
  ; x≤y⊔x     to i≤j⊔i        -- : ∀ i j → i ≤ j ⊔ i
  ; x≤y⇒x≤y⊔z to i≤j⇒i≤j⊔k    -- : ∀ {i j} k → i ≤ j → i ≤ j ⊔ k
  ; x≤y⇒x≤z⊔y to i≤j⇒i≤k⊔j    -- : ∀ {i j} k → i ≤ j → i ≤ k ⊔ j
  ; x⊔y≤z⇒x≤z to i⊔j≤k⇒i≤k    -- : ∀ i j {k} → i ⊔ j ≤ k → i ≤ k
  ; x⊔y≤z⇒y≤z to i⊔j≤k⇒j≤k    -- : ∀ i j {k} → i ⊔ j ≤ k → j ≤ k

  ; x⊓y≤x⊔y   to i⊓j≤i⊔j      -- : ∀ i j → i ⊓ j ≤ i ⊔ j
  )

⊔-identityˡ : LeftIdentity -∞ _⊔_
⊔-identityˡ -∞ = refl
⊔-identityˡ (fin x) = refl

⊔-identityʳ : RightIdentity -∞ _⊔_
⊔-identityʳ -∞ = refl
⊔-identityʳ (fin x) = refl

⊔-identity : Identity -∞ _⊔_
⊔-identity = ⊔-identityˡ , ⊔-identityʳ


i⊔fin≢-∞ : ∀ i j → i ⊔ fin j ≡ -∞ → ⊥
i⊔fin≢-∞ -∞ j ()
i⊔fin≢-∞ (fin x) j ()

-- Structures
⊔--∞-isMonoid : IsMonoid _⊔_ -∞
⊔--∞-isMonoid = record
  { isSemigroup = ⊔-isSemigroup
  ; identity    = ⊔-identity
  }

⊔--∞-isCommutativeMonoid : IsCommutativeMonoid _⊔_ -∞
⊔--∞-isCommutativeMonoid = record
  { isMonoid = ⊔--∞-isMonoid
  ; comm     = ⊔-comm
  }


-- + properties
+-comm : Commutative _+_
+-comm -∞ -∞ = refl
+-comm -∞ (fin x) = refl
+-comm (fin x) -∞ = refl
+-comm (fin x) (fin y) = cong fin (Data.Integer.Properties.+-comm x y)

+-identityˡ : LeftIdentity (fin Data.Integer.+0) _+_
+-identityˡ -∞ = refl
+-identityˡ (fin x) = cong fin (Data.Integer.Properties.+-identityˡ x)

+-identityʳ : RightIdentity (fin Data.Integer.+0) _+_
+-identityʳ -∞ = refl
+-identityʳ (fin x) = cong fin (Data.Integer.Properties.+-identityʳ x)

+-identity : Identity (fin Data.Integer.+0) _+_
+-identity = +-identityˡ , +-identityʳ

+-assoc : Associative _+_
+-assoc -∞ y z = refl
+-assoc (fin x) -∞ z = refl
+-assoc (fin x) (fin y) -∞ = refl
+-assoc (fin x) (fin y) (fin z) = cong fin (Data.Integer.Properties.+-assoc x y z)

-- Structures
+-isMagma : IsMagma _+_
+-isMagma = record
  { isEquivalence = Eq.isEquivalence
  ; ∙-cong        = cong₂ _+_
  }

+-isSemigroup : IsSemigroup _+_
+-isSemigroup = record
  { isMagma = +-isMagma
  ; assoc   = +-assoc
  }

+-isCommutativeSemigroup : IsCommutativeSemigroup _+_
+-isCommutativeSemigroup = record
  { isSemigroup = +-isSemigroup
  ; comm        = +-comm
  }

+-0-isMonoid : IsMonoid _+_ (fin Data.Integer.+0)
+-0-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity    = +-identity
  }

+-0-isCommutativeMonoid : IsCommutativeMonoid _+_ (fin Data.Integer.+0)
+-0-isCommutativeMonoid = record
  { isMonoid = +-0-isMonoid
  ; comm     = +-comm
  }

-- Bundles
+-magma : Magma 0ℓ 0ℓ
+-magma = record
  { isMagma = +-isMagma
  }

+-semigroup : Semigroup 0ℓ 0ℓ
+-semigroup = record
  { isSemigroup = +-isSemigroup
  }

+-commutativeSemigroup : CommutativeSemigroup 0ℓ 0ℓ
+-commutativeSemigroup = record
  { isCommutativeSemigroup = +-isCommutativeSemigroup
  }

+-0-monoid : Monoid 0ℓ 0ℓ
+-0-monoid = record
  { isMonoid = +-0-isMonoid
  }

+-0-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
+-0-commutativeMonoid = record
  { isCommutativeMonoid = +-0-isCommutativeMonoid
  }


-- + ⊔ properties

mono-≤-distrib-⊔ : ∀ {f} → f Preserves _≤_ ⟶ _≤_ → ∀ m n → f (m ⊔ n) ≡ f m ⊔ f n
mono-≤-distrib-⊔ {f} = ⊓-⊔-properties.mono-≤-distrib-⊔ (cong f)

+-monoˡ-≤ : ∀ n → (_+ n) Preserves _≤_ ⟶ _≤_
+-monoˡ-≤ -∞ -∞≤any = -∞≤any
+-monoˡ-≤ -∞ (fin≤fin _) = -∞≤any
+-monoˡ-≤ (fin x) -∞≤any = -∞≤any
+-monoˡ-≤ (fin x) (fin≤fin x≤y) = fin≤fin (Data.Integer.Properties.+-monoˡ-≤ x x≤y)

+-monoʳ-≤ : ∀ n → (_+_ n) Preserves _≤_ ⟶ _≤_
+-monoʳ-≤ -∞ x≤y = -∞≤any
+-monoʳ-≤ (fin x) -∞≤any = -∞≤any
+-monoʳ-≤ (fin x) (fin≤fin x≤y) = fin≤fin (Data.Integer.Properties.+-monoʳ-≤ x x≤y)

+-distribˡ-⊔ : _+_ DistributesOverˡ _⊔_
+-distribˡ-⊔ x y z = mono-≤-distrib-⊔ {_+_ x} (+-monoʳ-≤ x) y z

+-distribʳ-⊔ : _+_ DistributesOverʳ _⊔_
+-distribʳ-⊔ x y z = mono-≤-distrib-⊔ {λ y → y + x} (+-monoˡ-≤ x) y z

+-distrib-⊔ : _+_ DistributesOver _⊔_
+-distrib-⊔ = +-distribˡ-⊔ , +-distribʳ-⊔

+-zeroˡ : LeftZero -∞ _+_
+-zeroˡ _ = refl

+-zeroʳ : RightZero -∞ _+_
+-zeroʳ -∞ = refl
+-zeroʳ (fin x) = refl

+-zero : Zero -∞ _+_
+-zero = +-zeroˡ , +-zeroʳ

-- Structures

⊔-+-isSemiring : IsSemiring _⊔_ _+_ -∞ (fin Data.Integer.+0)
⊔-+-isSemiring = record
  { isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = ⊔--∞-isCommutativeMonoid
    ; *-isMonoid = +-0-isMonoid
    ; distrib = +-distrib-⊔
    }
  ; zero = +-zero
  }

⊔-+-isCommutativeSemiring : IsCommutativeSemiring _⊔_ _+_ -∞ (fin Data.Integer.+0)
⊔-+-isCommutativeSemiring = record
  { isSemiring = ⊔-+-isSemiring
  ; *-comm = +-comm
  }

-- Bundles

⊔-+-semiring : Semiring 0ℓ 0ℓ
⊔-+-semiring = record
  { isSemiring = ⊔-+-isSemiring
  }

⊔-+-commutativeSemiring : CommutativeSemiring 0ℓ 0ℓ
⊔-+-commutativeSemiring = record
  { isCommutativeSemiring = ⊔-+-isCommutativeSemiring
  }

-- - properties
i≡j∧j≢-∞⇒i-j≡0 : ∀ i j → i ≡ j → (j ≡ -∞ → ⊥) → i - j ≡ +0
i≡j∧j≢-∞⇒i-j≡0 i -∞ eq neq = ⊥-elim (neq refl)
i≡j∧j≢-∞⇒i-j≡0 .(fin x) (fin x) refl neq = cong fin (Data.Integer.Properties.m≡n⇒m-n≡0 x x refl)

