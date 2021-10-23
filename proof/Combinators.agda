module Combinators where

open import Agda.Primitive
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; trans; cong₂; cong-app; subst)
open import Data.List.Base as List
  using (List; []; _∷_; foldr; foldl; map; length; zip; unfold; reverse; concat; _++_)
open import Data.Product
  using (_,_; Σ; ∃; ∃-syntax; _×_; Σ-syntax; proj₁; proj₂)
open import Function
  using (_∘_; const; flip)
open import Data.Maybe.Base using (Maybe ; nothing; just)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Bool
open import Lens
open Lens.Lens
open import Core as Core



-- Bidirectional Fold
bfold : ∀ {S : Set} {V : Set} →
        (bxalg-data : Σ (Lens (Maybe (S × V)) V) λ l → l hasConditions (λ _ _ → ⊤) and (λ _ _ → ⊤)) →
        Lens (List S) V
bfold = Core.bxfold


-- Bidirectional Fold Preserving Length
bfold′ : ∀ {S : Set} {V : Set} →
         (bxalg-data : Σ (Lens (Maybe (S × V)) V) λ l → l hasConditions CommonConditions.keep-form (get l nothing) and (λ _ _ → ⊤)) →
         Lens (List S) V
bfold′ = Core.bxfold′


-- Bidirectional Map Preserving Length
bmap : ∀ {S V : Set} →
       (l-data : Σ (Lens S V) λ l → l hasConditions (λ _ _ → ⊤) and (λ _ _ → ⊤)) →
       Lens (List S) (List V)
bmap = Core.bxmap

-- Bidirectional Map Preserving Constraints on Adjacent Elements
bmapl : ∀ {S V : Set} →
        {P̃ : S → S → Set} →
        {Q̃ : V → V → Set} →
        (a₀ : S) →
        (l-data : Σ (Lens (S × S) (V × V))
                   λ l → l hasConditions (CommonConditions.map-dep-cond {S} P̃)
                           and            CommonConditions.map-dep-cond {V} Q̃) →
        (Σ (S → V) λ f →  (∀ {a a′} → get (proj₁ l-data) (a , a′) ≡ (f a , f a′))) →
        Lens (List S) (List V)
bmapl = Core.bxmap-depl


-- Bidirectional Map with Nested Bidirectional Fold
bfold-inits : ∀ {S V : Set} →
              {Q̃ : V → V → Set} →
              (b₀ : V) →
              (l-data : Σ (Lens (Maybe (S × V) × V) (V × V))
                        λ l → l hasConditions (CommonConditions.foldl-cond {S} {V} ) 
                                and            λ { (_ , b) (b′ , b′′) → Q̃ b b′ × b ≡ b′′ }) →
              (f-data
                : Σ (Maybe (S × V) → V)
                  λ f → (∀ {x} {y} → get (proj₁ l-data) (x , y) ≡ (f x , y)) × b₀ ≡ f nothing) →
              Lens (List S × List S) (V × V)
bfold-inits = Core.bxfoldl-inits



-- Bidirectional Scan
bscanl : ∀ {S V : Set} →
         {Q̃ : V → V → Set} →
         (b₀ : V) →
         (l-data : Σ (Lens (Maybe (S × V) × V) (V × V))
                         λ l → l hasConditions (CommonConditions.scanl-cond {S} {V}) 
                                 and            λ { (_ , b) (b′ , b′′) → Q̃ b b′ × b ≡ b′′ }) →
         (f-data
           : Σ (Maybe (S × V) → V)
             λ f → (∀ {x} {y} → get (proj₁ l-data) (x , y) ≡ (f x , y)) × b₀ ≡ f nothing) →
         Lens (List S) (List V)
bscanl = Core.bxscanl




