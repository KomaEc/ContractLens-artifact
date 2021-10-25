open import Agda.Primitive
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; trans; cong₂; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.List.Base as List
  using (List; []; _∷_; foldr; foldl; map; length; zip; unfold; reverse; concat; _++_)
open import Data.List.Properties
  using (++-cancelˡ; reverse-involutive; foldr-fusion; length-zipWith)
open import Data.Product
  using (_,_; Σ; ∃; ∃-syntax; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function
  using (_∘_; const; flip)
open import Data.Maybe.Base using (Maybe ; nothing; just)
open import Data.Empty using (⊥; ⊥-elim)
-- open import Data.Nat.Properties using (+-cancelˡ-<)
open import Data.Nat using (ℕ; suc; _+_; _<′_; _≤′_)
open import Data.Nat.Properties using (suc-injective; ⊓-idem)
open import Relation.Nullary using (Dec; yes; no)
open import Agda.Builtin.Unit using (⊤; tt)
open import Util using (η-⊤; transport′; funext)
open import Data.Maybe.Base using (just; nothing; maybe)
open import Data.Integer as ℤ renaming (suc to zsuc)
open import Data.Integer.DivMod using (_modℕ_)
open import Induction.WellFounded
open import Data.Nat.Induction
open import Data.IntegerOmega.Base hiding (-_)
open import Data.Integer using (+_; -_)
open import Data.Bool
open import Data.Float renaming (_≈_ to _f≈_; _+_ to _f+_; -_ to f-_)
import Agda.Builtin.Float
import Agda.Primitive
open import Lens
open Lens.Lens
open ≈-Reasoning
open import UniCombinatorsAndProperties
open import Core
open import Combinators
open import Theorems

module Examples where



-- The Fold Map Fusion Example in Overview Section
module Overview where

  even : ℤ → Bool
  even z with z modℕ 2 Data.Nat.≟ 0
  ... | yes _ = true
  ... | no  _ = false


  calculation :
    ∀ {A} →
    (cs : A → A → Set) →
    (ℓ-data : Σ (Lens A ℤ) λ ℓ → ℓ hasConditions cs and CommonConditions.true-cond) →
    bxmap2 cs CommonConditions.true-cond ℓ-data ； bfilter even [ (λ z → z) , (λ z → z) ]
    ≈
    bxfold-conditioned cs (CommonConditions.filter-cond CommonConditions.true-cond even) ((bmapf′ cs CommonConditions.true-cond (CommonConditions.filter-cond CommonConditions.true-cond even) ℓ-data  ； (bfilter-alg even) [ (λ z → z) , (λ z → z) ]) , refl , refl)
  calculation cs l-data = Theorems.bfold-map-fusion cs CommonConditions.true-cond (CommonConditions.filter-cond CommonConditions.true-cond even) l-data (bfilter-alg even , refl , refl)

    


module MaximumSegmentSum where

  binits : {A : Set} → Lens (List A) (List (List A))
  binits = Core.bxinits

  btails-inits : ∀ {A : Set} →
                 Lens (List A × List A)
                      ((∃[ xss ] (∃[ xs ] (tails {A} xs ≡ xss)))
                     × (∃[ xss ] (∃[ xs ] (tails {A} xs ≡ xss))))
  btails-inits = Core.bxtails-dep-init

  bmap-sum : Lens ((∃[ xss ] (∃[ xs ] (tails {ℤω} xs ≡ xss))) × (∃[ xss ] (∃[ xs ] (tails {ℤω} xs ≡ xss)))) (List ℤω × List ℤω)
  bmap-sum = Core.spec-bxmap-sum


  bmaximum2 : Lens (List ℤω × List ℤω) (ℤω × ℤω)
  bmaximum2 = Core.bxmaximum-dep

  bmaximum′ : Lens (List ℤω) ℤω
  bmaximum′ = Core.bxmaximum′


  bmss-defn : Lens (List ℤω) ℤω
  bmss-defn = binits ；
              bmapl [] (btails-inits , refl , refl) ((λ xs → tails xs , xs , refl) , (λ {a} {a′} → refl))
                [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
              bmapl ([] , [] , refl) (bmap-sum , refl , refl) ((λ { (xss , _ , _) → map sum xss}) , λ {a} {a′} → refl)
                [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
              bmapl [] (bmaximum2 , refl , refl) (maximum , refl)
                [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
              bmaximum′
                [ (λ {v} {v'} ∣v∣≡∣v'∣ → ConsecutivePairsProperties.cp-true , ∣v∣≡∣v'∣)
                , (λ { {v} {v'} (_ ,  ∣v∣≡∣v'∣) →  ∣v∣≡∣v'∣ }) ]


  bmss-intermediate₁ : Lens (List ℤω) ℤω
  bmss-intermediate₁ = binits ；
                       bmapl [] ((btails-inits ；
                                  bmap-sum
                                    [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
                                  bmaximum2
                                    [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ])
                                , refl , refl) ((λ xs → maximum (map sum (tails xs))) , (λ {a} {a′} → refl))
                             [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
                       bmaximum′
                         [ (λ {v} {v'} ∣v∣≡∣v'∣ → ConsecutivePairsProperties.cp-true , ∣v∣≡∣v'∣)
                         , (λ { {v} {v'} (_ ,  ∣v∣≡∣v'∣) →  ∣v∣≡∣v'∣ }) ]

  bmss-intermediate₂ : Lens (List ℤω) ℤω
  bmss-intermediate₂ = binits ；
                       bmapl []
                         ((bfold-inits -∞ (bx-⊕ , refl , refl) (⊕-listf , refl , refl)) , refl , refl)
                         (FoldlInits-Helper.g′ bx-⊕ -∞ , refl)
                         [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
                       bmaximum′
                         [ (λ {v} {v'} ∣v∣≡∣v'∣ → ConsecutivePairsProperties.cp-true , ∣v∣≡∣v'∣) , (λ { {v} {v'} (_ ,  ∣v∣≡∣v'∣) →  ∣v∣≡∣v'∣ }) ]


  bmss-optimized : Lens (List ℤω) ℤω
  bmss-optimized = bscanl -∞ (bx-⊕ , refl , refl) (⊕-listf , refl , refl) ；
                   bxmaximum′
                     [ (λ {v} {v'} ∣v∣≡∣v'∣ → ConsecutivePairsProperties.cp-true , ∣v∣≡∣v'∣)
                     , (λ { {v} {v'} (_ ,  ∣v∣≡∣v'∣) →  ∣v∣≡∣v'∣ }) ]


  module Helper where
    ℓ₁ = binits
    ℓ₂ = bmapl {S = List ℤω} [] (btails-inits , refl , refl) ((λ xs → tails xs , xs , refl) , (λ {a} {a′} → refl))
    ℓ₃ = bmapl ([] , [] , refl) (bmap-sum , refl , refl) ((λ { (xss , _ , _) → map sum xss}) , λ {a} {a′} → refl)
    ℓ₄ = bmapl [] (bmaximum2 , refl , refl) (maximum , refl)
    ℓ₅ = bmapl [] ((btails-inits ；
                   bmap-sum [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
                   bmaximum2 [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ])
                                , refl , refl) ((λ xs → maximum (map sum (tails xs))) , (λ {a} {a′} → refl))
    ℓ₅′ = bmapl [] ((btails-inits ；
                   bmap-sum [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ]) , refl , refl)
                   (map sum ∘ tails , (λ {a} {a′} → refl))
    ℓ₆ = bmapl [] ((bfold-inits -∞ (bx-⊕ , refl , refl) (⊕-listf , refl , refl)) , refl , refl)
                  (FoldlInits-Helper.g′ bx-⊕ -∞ , refl)
    ℓ₇ = bscanl -∞ (bx-⊕ , refl , refl) (⊕-listf , refl , refl)


  step₁ : bmss-defn ≈ bmss-intermediate₁
  step₁ = ≈-trans bmss-defn
                   (ℓ₁ ；
                   (ℓ₂ ；
                   ℓ₃ [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
                   ℓ₄ [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ])
                     [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
                   bmaximum′
                     [ (λ {v} {v'} ∣v∣≡∣v'∣ → ConsecutivePairsProperties.cp-true , ∣v∣≡∣v'∣)
                     , (λ { {v} {v'} (_ ,  ∣v∣≡∣v'∣) →  ∣v∣≡∣v'∣ }) ])
                   bmss-intermediate₁
                   step₁₁
                   step₁₂
    where
      open Helper
      step₁₁ : bmss-defn ≈
               ℓ₁ ；
               (ℓ₂ ；
               ℓ₃ [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
               ℓ₄ [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ]) [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
               bmaximum′
                 [ (λ {v} {v'} ∣v∣≡∣v'∣ → ConsecutivePairsProperties.cp-true , ∣v∣≡∣v'∣)
                 , (λ { {v} {v'} (_ ,  ∣v∣≡∣v'∣) →  ∣v∣≡∣v'∣ }) ]
      step₁₁ = ；-congˡ (ℓ₁ ；
                         ℓ₂ [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
                         ℓ₃ [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
                         ℓ₄ [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ])
                         (ℓ₁ ；
                         (ℓ₂ ；
                         ℓ₃  [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
                         ℓ₄ [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ]) [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ])
                         bmaximum′
                         ((λ {v} {v'} ∣v∣≡∣v'∣ → ConsecutivePairsProperties.cp-true , ∣v∣≡∣v'∣)
                         , (λ { {v} {v'} (_ ,  ∣v∣≡∣v'∣) →  ∣v∣≡∣v'∣ }))
                         ((λ {v} {v'} ∣v∣≡∣v'∣ → ConsecutivePairsProperties.cp-true , ∣v∣≡∣v'∣)
                         , (λ { {v} {v'} (_ ,  ∣v∣≡∣v'∣) →  ∣v∣≡∣v'∣ }))
                         (；-assoc₄ ℓ₁ ℓ₂ ℓ₃ ℓ₄
                                    ((λ {v} {v'} z → z) , (λ {v} {v'} z → z))
                                    ((λ {v} {v'} z → z) , (λ {v} {v'} z → z))
                                    ((λ {v} {v'} z → z) , (λ {v} {v'} z → z)))
      fusion₁ : ℓ₂ ；
                ℓ₃ [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ]
                ≈
                ℓ₅′
      fusion₁ = Theorems.bmapl-fusion []
                                      (btails-inits , refl , refl)
                                      ((λ xs → tails xs , xs , refl) , (λ {a} {a′} → refl))
                                      (bmap-sum , refl , refl) ((λ { (xss , _ , _) → map sum xss}) , λ {a} {a′} → refl) 
      fusion₂ : ℓ₅′ ；
                ℓ₄ [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ]
                ≈
                ℓ₅
      fusion₂ = Theorems.bmapl-fusion []
                                      ((btails-inits ； bmap-sum
                                        [ (λ {v} {v'} z → z)
                                        , (λ {v} {v'} z → z) ]) , refl , refl)
                                      (map sum ∘ tails , (λ {a} {a′} → refl))
                                      (bmaximum2 , refl , refl) (maximum , refl)
      fusion : ℓ₂ ；
               ℓ₃ [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
               ℓ₄ [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ]
               ≈
               ℓ₅
      fusion = ≈-trans  (ℓ₂ ； ℓ₃ [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
                         ℓ₄ [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ])
                         (ℓ₅′ ； ℓ₄ [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ])
                         ℓ₅
                         (；-congˡ (ℓ₂ ； ℓ₃ [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ])
                           ℓ₅′
                           ℓ₄
                           ((λ {v} {v'} z → z) , (λ {v} {v'} z → z))
                           ((λ {v} {v'} z → z) , (λ {v} {v'} z → z)) fusion₁)
                         fusion₂
      step₁₂ : ℓ₁ ；
               (ℓ₂ ；
               ℓ₃ [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
               ℓ₄ [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ]) [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
               bmaximum′
                 [ (λ {v} {v'} ∣v∣≡∣v'∣ → ConsecutivePairsProperties.cp-true , ∣v∣≡∣v'∣)
                 , (λ { {v} {v'} (_ ,  ∣v∣≡∣v'∣) →  ∣v∣≡∣v'∣ }) ]
               ≈
               ℓ₁ ；
               ℓ₅ [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
               bmaximum′
                 [ (λ {v} {v'} ∣v∣≡∣v'∣ → ConsecutivePairsProperties.cp-true , ∣v∣≡∣v'∣)
                 , (λ { {v} {v'} (_ ,  ∣v∣≡∣v'∣) →  ∣v∣≡∣v'∣ }) ]
      step₁₂ = ；-congᵐ ℓ₁
                         (ℓ₂ ；
                         ℓ₃ [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
                         ℓ₄ [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ])
                         ℓ₅
                         bmaximum′
                         ((λ {v} {v'} z → z) , (λ {v} {v'} z → z))
                         ((λ {v} {v'} ∣v∣≡∣v'∣ → ConsecutivePairsProperties.cp-true , ∣v∣≡∣v'∣)
                         , (λ { {v} {v'} (_ ,  ∣v∣≡∣v'∣) →  ∣v∣≡∣v'∣ }))
                         ((λ {v} {v'} z → z) , (λ {v} {v'} z → z))
                         ((λ {v} {v'} ∣v∣≡∣v'∣ → ConsecutivePairsProperties.cp-true , ∣v∣≡∣v'∣)
                         , (λ { {v} {v'} (_ ,  ∣v∣≡∣v'∣) →  ∣v∣≡∣v'∣ })) fusion


  step₂ : bmss-intermediate₁ ≈ bmss-intermediate₂
  step₂ = ；-congᵐ ℓ₁
                    ℓ₅ ℓ₆
                    bmaximum′
                    ((λ {v} {v'} z → z) , (λ {v} {v'} z → z))
                         ((λ {v} {v'} ∣v∣≡∣v'∣ → ConsecutivePairsProperties.cp-true , ∣v∣≡∣v'∣)
                         , (λ { {v} {v'} (_ ,  ∣v∣≡∣v'∣) →  ∣v∣≡∣v'∣ }))
                         ((λ {v} {v'} z → z) , (λ {v} {v'} z → z))
                         ((λ {v} {v'} ∣v∣≡∣v'∣ → ConsecutivePairsProperties.cp-true , ∣v∣≡∣v'∣)
                         , (λ { {v} {v'} (_ ,  ∣v∣≡∣v'∣) →  ∣v∣≡∣v'∣ }))
                   (Core.bxmap-depl-cong
                     []
                     ((btails-inits ；
                       bmap-sum [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
                       bmaximum2 [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ]) , refl , refl)
                     ((λ xs → maximum (map sum (tails xs))) , (λ {a} {a′} → refl))
                     ((bfold-inits -∞ (bx-⊕ , refl , refl) (⊕-listf , refl , refl)) , refl , refl)
                     (FoldlInits-Helper.g′ bx-⊕ -∞ , refl) Core.uni-hornor-rule Theorems.modified-hornor's-rule)
    where
      open Helper


  step₃ : bmss-intermediate₂ ≈ bmss-optimized
  step₃ = ；-congˡ (ℓ₁ ； ℓ₆ [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ])
                    ℓ₇
                    bmaximum′
                    ((λ {v} {v'} ∣v∣≡∣v'∣ → ConsecutivePairsProperties.cp-true , ∣v∣≡∣v'∣)
                    , (λ { {v} {v'} (_ ,  ∣v∣≡∣v'∣) →  ∣v∣≡∣v'∣ }))
                    ((λ {v} {v'} ∣v∣≡∣v'∣ → ConsecutivePairsProperties.cp-true , ∣v∣≡∣v'∣)
                    , (λ { {v} {v'} (_ ,  ∣v∣≡∣v'∣) →  ∣v∣≡∣v'∣ }))
                    (Theorems.bscanl-lemma -∞ (bx-⊕ , refl , refl) (⊕-listf , refl , refl))
    where
      open Helper
               


  bmss-calculation : bmss-defn ≈ bmss-optimized
  bmss-calculation
    = ≈-trans bmss-defn bmss-intermediate₁ bmss-optimized
              step₁ (≈-trans bmss-intermediate₁ bmss-intermediate₂ bmss-optimized
                             step₂ step₃)


  
  module _ where

    example-list : List ℤω
    example-list = fin (+ 31) ∷ fin (- (+ 41)) ∷ fin (+ 59) ∷ fin (+ 26) ∷ fin (- (+ 53)) ∷ fin (+ 58) ∷ fin (+ 97) ∷ fin (- (+ 93)) ∷ fin (- (+ 23)) ∷ fin (+ 24) ∷ []

    _ : get bmss-defn example-list ≡ fin (+ 187)
    _ = refl

    _ : get bmss-optimized example-list ≡ fin (+ 187)
    _ = refl

    _ : put bmss-optimized example-list (fin (+ 128)) ≡ fin (+ 31) ∷ fin (- (+ 41)) ∷ fin (+ 59) ∷ fin (+ 26) ∷ fin (- (+ 53)) ∷ fin (+ 58) ∷ fin (+ 38) ∷ fin (- (+ 34)) ∷ fin (- (+ 23)) ∷ fin (+ 24) ∷ []
    _ = refl

    _ : get bmss-optimized (fin (+ 31) ∷ fin (- (+ 41)) ∷ fin (+ 59) ∷ fin (+ 26) ∷ fin (- (+ 53)) ∷ fin (+ 58) ∷ fin (+ 38) ∷ fin (- (+ 34)) ∷ fin (- (+ 23)) ∷ fin (+ 24) ∷ []) ≡ fin (+ 128)
    _ = refl

  
