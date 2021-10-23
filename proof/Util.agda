module Util where


open import Agda.Primitive
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; trans; cong₂; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.List.Base as List
  using (List; []; _∷_; foldr; map; scanr; _++_; length)
open import Data.Product
  using (_,_; Σ; ∃; ∃-syntax; _×_; Σ-syntax)
open import Function
  using (_∘_)
open import Data.Maybe.Base using (Maybe ; nothing; just)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Agda.Builtin.Unit using (⊤; tt)
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

private
  variable
    ℓ ℓ′ : Level

η-⊤ : ∀ (w : ⊤) → w ≡ tt
η-⊤ w = refl

transport′ : ∀ {P Q : Set} → P ≡ Q → P → Q
transport′ refl x = x

postulate
      funext : {X : Set ℓ} → {Y : X → Set ℓ} →
               ∀ {f g : (x : X) → Y x} → (∀ x → f x ≡ g x) → f ≡ g

funext' : {X : Set ℓ} {Y : X → Set ℓ} →
          ∀ {f g : ∀ {x : X} → Y x} → (∀ x → f {x} ≡ g {x}) → _≡_ {A = ∀ {x : X} → Y x} f g
funext' {f = f} {g = g} q = cong (λ f {x} → f x) (funext {f = λ x → f {x}} {g = λ x → g {x}} q)


unique-id-proof : ∀ {X : Set} {x y : X} {p q : x ≡ y} → p ≡ q
unique-id-proof {p = refl} {refl} = refl

-- Lebniz Equality

_≐_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y

refl-≐ : ∀ {A : Set ℓ} {x : A}
  → x ≐ x
refl-≐ P Px  =  Px

trans-≐ : ∀ {A : Set ℓ} {x y z : A}
  → x ≐ y
  → y ≐ z
    -----
  → x ≐ z
trans-≐ x≐y y≐z P Px  =  y≐z P (x≐y P Px)

sym-≐ : ∀ {ℓ : Level} {A : Set ℓ} {x y : A}
  → x ≐ y
    -----
  → y ≐ x
sym-≐ {ℓ} {A} {x} {y} x≐y P  =  Qy
  where
    Q : A → Set ℓ
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = x≐y Q Qx

≐-implies-≡ : ∀ {ℓ : Level} {A : Set ℓ} {x y : A}
  → x ≐ y
    -----
  → x ≡ y
≐-implies-≡ {ℓ} {A} {x} {y} x≐y  =  Qy
  where
    Q : A → Set ℓ
    Q z = x ≡ z
    Qx : Q x
    Qx = refl
    Qy : Q y
    Qy = x≐y Q Qx


case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x


