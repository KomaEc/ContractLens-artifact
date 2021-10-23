

module Data.IntegerOmega.Base where

open import Level using (0ℓ)

open import Data.Bool using (Bool; true; false)
open import Data.Sum using (inj₁; inj₂; map)

import Data.Nat as Nat
import Data.Integer as Int
import Data.Integer.Properties as Int
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Empty using (⊥; ⊥-elim)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)

open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; map′)
open import Relation.Binary


-- open import Show

data ℤω : Set where
  -∞ : ℤω
  fin : ℤ → ℤω


+0 : ℤω
+0 = fin Data.Integer.+0

{-
instance
  ℤω-Showable : Showable ℤω
  ℤω-Showable .show -∞      = "-∞"
  ℤω-Showable .show (fin n) = show n
-}

infix 4 _≤_ _≥_ _<_ _>_ _≰_ _≱_ _≮_ _≯_

data _≤_ : ℤω → ℤω → Set where
  -∞≤any : ∀ {x : ℤω} → -∞ ≤ x
  fin≤fin : ∀ {x y : ℤ} → x Int.≤ y → fin x ≤ fin y

data _<_ : ℤω → ℤω → Set where
  -∞<any : ∀ {x : ℤω} → -∞ < x
  fin<fin : ∀ {x y : ℤ} → x Int.< y → fin x < fin y

_≥_ : ℤω → ℤω → Set
x ≥ y = y ≤ x

_>_ : Rel ℤω 0ℓ
x > y = y < x

_≰_ : Rel ℤω 0ℓ
x ≰ y = (x ≤ y) → ⊥

_≱_ : Rel ℤω 0ℓ
x ≱ y = (x ≥ y) → ⊥

_≮_ : Rel ℤω 0ℓ
x ≮ y = (x < y) → ⊥

_≯_ : Rel ℤω 0ℓ
x ≯ y = (x > y) → ⊥




-- general
fin-injective : ∀ {x y} → fin x ≡ fin y → x ≡ y
fin-injective refl = refl


_≟_ : Decidable {A = ℤω} _≡_
-∞    ≟ -∞    = yes refl
fin x ≟ fin y = map′ (cong fin) fin-injective (x Int.≟ y)
-∞    ≟ fin _ = no λ()
fin _ ≟ -∞    = no λ()

_≤?_ : Decidable _≤_
-∞ ≤? j = yes -∞≤any
fin x ≤? -∞ = no λ ()
fin x ≤? fin y with x Int.≤? y
... | yes prf = yes (fin≤fin prf)
... | no absurd = no λ { (fin≤fin prf) → absurd prf }

_≡ᵇ_ : ℤω → ℤω → Bool
x ≡ᵇ y = ⌊ x ≟ y ⌋

infixl 7 _⊓_
infixl 6 _⊔_

_⊔_ : ℤω → ℤω → ℤω
-∞    ⊔ y     = y
x     ⊔ -∞    = x
fin x ⊔ fin y = fin (x Int.⊔ y)

_⊓_ : ℤω → ℤω → ℤω
-∞    ⊓ _     = -∞
_     ⊓ -∞    = -∞
fin x ⊓ fin y = fin (x Int.⊓ y)



infix  8 -_
infixl 6 _+_ _-_

_+_ : ℤω → ℤω → ℤω
-∞ + y = -∞
fin x + -∞ = -∞
fin x + fin y = fin (x Data.Integer.+ y)


-_ : ℤω → ℤω
- -∞ = +0 -- absurd branch
- fin x = fin (Data.Integer.- x)

_-_ : ℤω → ℤω → ℤω
x - y = x + (- y)
