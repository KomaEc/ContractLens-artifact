module Theorems where

open import Agda.Primitive
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.List.Base as List
  using (List; []; _∷_; foldr; foldl; map; length; zip; unfold; reverse; concat; _++_)
open import Data.Product
  using (_,_; Σ; ∃; ∃-syntax; _×_; Σ-syntax; proj₁; proj₂)
open import Function
  using (_∘_; const; flip)
open import Data.Maybe.Base using (Maybe ; nothing; just)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; suc; _+_; _<′_; _≤′_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Maybe.Base using (just; nothing; maybe)
open import Data.IntegerOmega.Base
open import Data.Bool

open import Util
open import Lens
open Lens.Lens
open import Core
open import Combinators
open import UniCombinatorsAndProperties



-- Bidirectional Fold Fusion Law
bfold-fusion : ∀ {S : Set} {V T : Set} →                                                    
                (l : Lens V T) →
                (l-conds : l hasConditions (λ _ _ → ⊤) and (λ _ _ → ⊤)) →
                {bxalg₁-data : Σ (Lens (Maybe (S × V)) V) λ l → l hasConditions (λ _ _ → ⊤) and (λ _ _ → ⊤)} →
                {bxalg₂-data : Σ (Lens (Maybe (S × T)) T) λ l → l hasConditions (λ _ _ → ⊤) and (λ _ _ → ⊤)} →
                  ((proj₁ bxalg₁-data) ； l
                               [ (λ {v} {v'} _ → transport′ (sym (cong (λ pred → pred v v')  (proj₂ (proj₂ bxalg₁-data)))) tt) , (λ {v} {v'} _ → transport′ (sym (cong (λ pred → pred v v')  (proj₁ l-conds))) tt) ] )
                ≈
                  (blistf (get (proj₁ bxalg₁-data) nothing) (l , l-conds) ； (proj₁ bxalg₂-data)
                               [ (λ {v} {v'} _ → tt) , (λ {v} {v'} _ → transport′ (sym (cong (λ pred → pred v v')  (proj₁ (proj₂ bxalg₂-data)))) tt) ] )
                →
                  (bxfold bxalg₁-data  ； l
                               [ (λ {v} {v'} _ → tt) , (λ {v} {v'} _ → transport′ (sym (cong (λ pred → pred v v')  (proj₁ l-conds))) tt) ])
                ≈
                  bxfold bxalg₂-data
bfold-fusion = Core.bxfold-fusion


bfold′-fusion : ∀ {S V T : Set} →
                 (cs : S → S → Set) →
                 (cv : V → V → Set) →
                 (ct : T → T → Set) →
                 (bxalg₁-data : Σ (Lens (Maybe (S × V)) V)
                               λ l → l hasConditions (CommonConditions.lift cs cv)
                                       and           cv) →
                 (l-data : Σ (Lens V T) λ l → l hasConditions cv and ct) →
                 (bxalg₂-data : Σ (Lens (Maybe (S × T)) T)
                               λ l → l hasConditions (CommonConditions.lift cs ct)
                                     and             ct) →
                 ((proj₁ bxalg₁-data ； proj₁ l-data
                          -- composition condition
                          [ (λ {v} {v′} cvvv → transport′ (sym (cong (λ pred → pred v v′)  (proj₂ (proj₂ bxalg₁-data)))) (transport′ (cong (λ pred → pred v v′) (proj₁ (proj₂ l-data))) cvvv)) , (λ {v} {v′} cvvv → transport′ (sym (cong (λ pred → pred v v′)  (proj₁ (proj₂ l-data)))) (transport′ (cong (λ pred → pred v v′) (proj₂ (proj₂ bxalg₁-data))) cvvv)) ])
                 ≈ blistf′ cs cv ct l-data ； proj₁ bxalg₂-data
                           -- composition condition
                           [ (λ {v} {v′} cvv → transport′ (cong (λ pred → pred v v′) (proj₁ (proj₂ bxalg₂-data))) cvv)  , (λ {v} {v′} cvv → transport′ (cong (λ pred → pred v v′) (sym (proj₁ (proj₂ bxalg₂-data)))) cvv) ] )
                 →
                 bxfold-conditioned cs cv bxalg₁-data ； proj₁ l-data
                           -- composition condition
                           [ (λ {v} {v′} → transport′ (cong-app (cong-app (proj₁ (proj₂ l-data)) v) v′))  , (λ {v} {v′} → transport′ (cong-app (cong-app (sym (proj₁ (proj₂ l-data))) v) v′)) ]
                 ≈ bxfold-conditioned cs ct bxalg₂-data
bfold′-fusion = Core.bxfold′-fusion



-- Bidirectional Map Fusion Law
bmapl-fusion
  : ∀ {S V T : Set} →
    (a₀ : S) →
    {P̃ : S → S → Set} →
    {Q̃ : V → V → Set} →
    {R̃ : T → T → Set} →
    (l₁-data : Σ (Lens (S × S) (V × V))
                       λ l → l hasConditions (λ { (_ , a) (a′ , a′′) → P̃ a a′ × a ≡ a′′})
                               and            λ { (_ , b) (b′ , b′′) → Q̃ b b′ × b ≡ b′′}) →
    (f₁-data : Σ (S → V) λ f →  (∀ {a a′} → get (proj₁ l₁-data) (a , a′) ≡ (f a , f a′))) →
    (l₂-data : Σ (Lens (V × V) (T × T))
                       λ l → l hasConditions (λ { (_ , a) (a′ , a′′) → Q̃ a a′ × a ≡ a′′})
                               and            λ { (_ , b) (b′ , b′′) → R̃ b b′ × b ≡ b′′}) →
    (f₂-data : Σ (V → T) λ f →  (∀ {a a′} → get (proj₁ l₂-data) (a , a′) ≡ (f a , f a′))) →
    
    (bxmap-depl a₀ l₁-data f₁-data ； bxmap-depl (proj₁ f₁-data a₀) l₂-data f₂-data [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ])
    
    ≈
    
    (bxmap-depl a₀ (((proj₁ l₁-data ； proj₁ l₂-data
      [ (λ {v} {v'} p → transport′
                          (cong (λ pred → pred v v')
                                (sym (trans (proj₂ (proj₂ l₁-data))
                                            (sym (proj₁ (proj₂ l₂-data)))))) p)
      , (λ {v} {v'} p → transport′
                          (cong (λ pred → pred v v')
                                (trans (proj₂ (proj₂ l₁-data))
                                       (sym (proj₁ (proj₂ l₂-data))))) p) ]))
                      , (proj₁ (proj₂ l₁-data)) , proj₂ (proj₂ l₂-data))
                    ((proj₁ f₂-data ∘ proj₁ f₁-data)
                    , λ {a} {a′} → begin
                                     get (proj₁ l₂-data) (get (proj₁ l₁-data) (a , a′))
                                   ≡⟨ cong (get (proj₁ l₂-data)) (proj₂ f₁-data) ⟩
                                     get (proj₁ l₂-data) (proj₁ f₁-data a , proj₁ f₁-data a′)
                                   ≡⟨ proj₂ f₂-data ⟩
                                     ((proj₁ f₂-data) ∘ (proj₁ f₁-data)) a , ((proj₁ f₂-data) ∘ (proj₁ f₁-data)) a′
                                   ∎))
bmapl-fusion = Core.bxmap-depl-fusion




-- Bidirectional Fold Map Fusion Law

bfold-map-fusion : ∀ {S V T} →
                     (cs : S → S → Set) →
                     (cv : V → V → Set) →
                     (ct : T → T → Set) →
                     (l-data : Σ (Lens S V) (λ l → l hasConditions cs and cv)) →
                     (bxalg-data : Σ (Lens (Maybe (V × T)) T) λ l → l hasConditions (CommonConditions.lift cv ct) and ct) →
                     bxmap2 cs cv l-data ； bxfold-conditioned cv ct bxalg-data [ (λ z → z) , (λ z → z) ]
                     ≈
                     bxfold-conditioned cs ct ((bmapf′ cs cv ct l-data ；  proj₁ bxalg-data
                                                [ (λ {v} {v'} cond → transport′ (cong (λ pred → pred v v') (proj₁ (proj₂ bxalg-data))) cond)
                                                , ((λ {v} {v'} cond → transport′ (sym (cong (λ pred → pred v v') (proj₁ (proj₂ bxalg-data))) ) cond)) ])
                                                , refl , (proj₂ (proj₂ bxalg-data)))
bfold-map-fusion = Core.bxfold-map-fusion′


-- Bidirectional Scanl Lemma
bscanl-lemma : ∀ {S V : Set} →
               {Q̃ : V → V → Set} →
               (b₀ : V) →
               (l-data : Σ (Lens (Maybe (S × V) × V) (V × V))
                         λ l → l hasConditions (CommonConditions.scanl-cond {S} {V} ) 
                                 and            λ { (_ , b) (b′ , b′′) → Q̃ b b′ × b ≡ b′′ }) →
               (f-data
                 : Σ (Maybe (S × V) → V)
                   λ f → (∀ {x} {y} → get (proj₁ l-data) (x , y) ≡ (f x , y))) →
                
               bxinits ； (bxmap-depl {P̃ = CommonConditions.is-init} {Q̃ = Q̃}
                                       []
                                       (bxfoldl-inits b₀ l-data f-data
                                       , refl , refl) (FoldlInits-Helper.g′ (proj₁ l-data) b₀ , λ {a} {a′} → refl))
                             [ (λ {v} {v'} z → z)
                             , (λ {v} {v'} z → z) ]
               ≈
               bxscanl b₀ l-data f-data
bscanl-lemma = Core.bxscanl-lemma



-- Modified Hornor's Rule
modified-hornor's-rule : bxtails-dep-init ；
                         spec-bxmap-sum [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
                         bxmaximum-dep [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ]
                         ≈
                         bxfoldl-inits {Q̃ = CommonConditions.true-cond} -∞ (bx-⊕ , refl , refl) (⊕-listf , refl)
modified-hornor's-rule = Core.hornor-rule
