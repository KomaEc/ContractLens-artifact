module Lens where

open import Agda.Primitive
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.List.Base as List
  using (List; []; _∷_; foldr; map; scanr; _++_)
open import Data.Product
  using (_,_; Σ; ∃; ∃-syntax; _×_; Σ-syntax; proj₁; proj₂)
open import Function
  using (_∘_)
open import Data.Maybe.Base using (Maybe ; nothing; just)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Nat

open import Util using (transport′; funext; funext'; unique-id-proof)

record Lens {l : Level} (S : Set l) (V : Set l) : Set (lsuc l) where
  field
    get : S → V
    put : S → V → S
    P : S → S → Set
    Q : V → V → Set

    backward-validity : ∀ {a : S} {b : V} → Q (get a) b → P a (put a b)

    forward-validity : ∀ {a : S} → P a a → Q (get a) (get a)

    conditioned-get-put : ∀ {a : S} → P a a → put a (get a) ≡ a

    conditioned-put-get : ∀ {a : S} {b : V} → Q (get a) b → get (put a b) ≡ b
    
open Lens


general-compose
  : {S V T : Set} → (l₁ : Lens S V) → (l₂ : Lens V T)
    → (implication₁ : ∀ {v v′ : V} → P l₂ v v′ → Q l₁ v v′)
    → (implication₂ : ∀ {v : V} → Q l₁ v v → P l₂ v v)
    → Lens S T
general-compose {S} {V} l₁ l₂ impl impl′ = record
                      { get = get l₂ ∘ get l₁
                      ; put = λ s v → put l₁ s (put l₂ (get l₁ s) v) 
                      ; P = P l₁
                      ; Q = Q l₂
                      ; backward-validity = backward-validity l₁ ∘ impl ∘ backward-validity l₂
                      ; forward-validity = forward-validity l₂ ∘ impl′ ∘ forward-validity l₁
                      ; conditioned-get-put
                          = λ {a} cond → begin
                                           put l₁ a (put l₂ (get l₁ a) (get l₂ (get l₁ a)))
                                         ≡⟨ cong (put l₁ a) (conditioned-get-put l₂ (impl′ (forward-validity l₁ cond))) ⟩
                                           put l₁ a (get l₁ a)
                                         ≡⟨ conditioned-get-put l₁ cond ⟩
                                           a
                                         ∎
                      ; conditioned-put-get
                          = λ {a} {b} cond → begin
                                               get l₂ (get l₁ (put l₁ a (put l₂ (get l₁ a) b)))
                                             ≡⟨ cong (get l₂) (conditioned-put-get l₁ ((impl ∘ backward-validity l₂) cond)) ⟩
                                               get l₂ (put l₂ (get l₁ a) b)
                                             ≡⟨ conditioned-put-get l₂ cond ⟩
                                               b
                                             ∎
                      }
                        


compose-cond : ∀ {S V T : Set} →
               (ℓ₁ : Lens S V) (ℓ₂ : Lens V T) →
               Set
compose-cond ℓ₁ ℓ₂ = (∀ {v v′} → P ℓ₂ v v′ → Q ℓ₁ v v′) × (∀ {v v′} → Q ℓ₁ v v′ → P ℓ₂ v v′)

-- \;5
_；_[_] : {S V T : Set} → (l₁ : Lens S V) → (l₂ : Lens V T)
    -- → (implication₁ : ∀ {v v' : V} → P l₂ v v' → Q l₁ v v')
    -- → (implication₂ : ∀ {v v' : V} → Q l₁ v v' → P l₂ v v')
    → compose-cond l₁ l₂
    → Lens S T
_；_[_] {S} {V} l₁ l₂ (impl , impl′) = general-compose {S} {V} l₁ l₂ impl (λ {v} → impl′ {v} {v})


_；_ : {S V T : Set} → (l₁ : Lens S V) → (l₂ : Lens V T) →
       {implication₁ : ∀ {v v' : V} → P l₂ v v' → Q l₁ v v'} →
       {implication₂ : ∀ {v v' : V} → Q l₁ v v' → P l₂ v v'} →
       Lens S T
_；_ l₁ l₂ {impl} {impl′} = l₁ ； l₂ [ impl , impl′ ]



lens-derive : ∀ {S V : Set} →
              (ℓ : Lens S V) →
              (g : S → V) → (p : S → V → S) →
              (∀ {s : S} → get ℓ s ≡ g s) →
              (∀ {s : S} {v : V} → Q ℓ (get ℓ s) v → put ℓ s v ≡ p s v) →
              Lens S V
lens-derive {S} {V} ℓ g p get-eq put-eq
  = record
      { get = g
      ; put = p
      ; P = P ℓ
      ; Q = Q ℓ
      ; backward-validity = λ {a} {b} → prop₁ a b
      ; forward-validity = λ {a} → prop₂ a
      ; conditioned-get-put = λ {a} → cgp a
      ; conditioned-put-get = λ {a} {b} → cpg a b
      }
  where
    prop₁ : (a : S) (b : V) → Q ℓ (g a) b → P ℓ a (p a b)
    prop₁ a b q rewrite sym (get-eq {a}) | sym (put-eq q) = backward-validity ℓ q
    prop₂ : (a : S) → P ℓ a a → Q ℓ (g a) (g a)
    prop₂ a p rewrite sym (get-eq {a}) = forward-validity ℓ p
    cgp : (a : S) → P ℓ a a → p a (g a) ≡ a
    cgp a Paa rewrite sym (get-eq {a}) | sym (put-eq (forward-validity ℓ Paa)) = conditioned-get-put ℓ Paa
    cpg : (a : S) (b : V) → Q ℓ (g a) b → g (p a b) ≡ b
    cpg a b Qab rewrite sym (get-eq {p a b}) | sym (get-eq {a}) | sym (put-eq Qab) = conditioned-put-get ℓ Qab


lens-equiv : ∀ {S V : Set} → (l₁ l₂ : Lens S V) → Set₁
lens-equiv {S} {V} l₁ l₂
  = (∀ {s s′ : S} → P l₁ s s′ ≡ P l₂ s s′)
     ×
       (∀ {v v′ : V} → Q l₁ v v′ ≡ Q l₂ v v′)
         ×
           (∀ {s : S} → get l₁ s ≡ get l₂ s)
           × (∀ {s : S} {v : V} → Q l₁ (get l₁ s) v → put l₁ s v ≡ put l₂ s v)


_≈_ : ∀ {S V : Set} → (l₁ l₂ : Lens S V) → Set₁
_≈_ = lens-equiv

infix 4 _≈_

≈-refl : ∀ {S V : Set} → (l : Lens S V) →
         l ≈ l
≈-refl l = (λ {s} {s′} → refl) , (λ {v} {v′} → refl) , (λ {s} → refl) , λ {s} {v} q → refl

≈-sym : ∀ {S V : Set} → (l₁ l₂ : Lens S V) →
        l₁ ≈ l₂ → l₂ ≈ l₁
≈-sym l₁ l₂ (P-eq , Q-eq , get-eq , put-eq)
  = (λ {s} {s′} → sym P-eq)
  , (λ {v} {v′} → sym Q-eq)
  , (λ {s} → sym get-eq)
  , λ {s} {v} q → put-eq′ s v q
  where
    put-eq′ : ∀ s v → Q l₂ (get l₂ s) v → put l₂ s v ≡ put l₁ s v
    put-eq′ s v q with get l₂ s | sym (get-eq {s})
    ... | .(get l₁ s) | refl with Q l₂ (get l₁ s) v | sym (Q-eq {get l₁ s} {v})
    ... | .(Q l₁ (get l₁ s) v) | refl = sym (put-eq q)

≈-trans′ : ∀ {S V : Set} → {l₁ l₂ l₃ : Lens S V} →
          l₁ ≈ l₂ → l₂ ≈ l₃ → l₁ ≈ l₃
≈-trans′ {S} {V} {l₁} {l₂} {l₃} (P-eq , Q-eq , get-eq , put-eq) (P-eq' , Q-eq' , get-eq' , put-eq')
  = trans P-eq P-eq'
  , trans Q-eq Q-eq'
  , trans get-eq get-eq'
  , λ {s} {v} → put-eq′ s v
  where
    put-eq′ : ∀ s v → Q l₁ (get l₁ s) v → put l₁ s v ≡ put l₃ s v
    put-eq′ s v q  with put-eq' {s} {v}
    ... | put-eq'' with get l₂ s | sym (get-eq {s})
    ... | .(get l₁ s) | refl with Q l₂ (get l₁ s) v | sym (Q-eq {get l₁ s} {v})
    ... | .(Q l₁ (get l₁ s) v) | refl = trans (put-eq q) (put-eq'' q)

≈-trans : ∀ {S V : Set} → (l₁ l₂ l₃ : Lens S V) →
          l₁ ≈ l₂ → l₂ ≈ l₃ → l₁ ≈ l₃
≈-trans l₁ l₂ l₃ = ≈-trans′ {l₁ = l₁} {l₂ = l₂} {l₃ = l₃}

；-congˡ : ∀ {S V T : Set} →
           (l₁ l₂ : Lens S V) →
           (l₃ : Lens V T) →
           (cond₁ : compose-cond l₁ l₃) →
           (cond₂ : compose-cond l₂ l₃) →
           l₁ ≈ l₂ →
           l₁ ； l₃ [ cond₁ ]
           ≈
           l₂ ； l₃ [ cond₂ ]
；-congˡ {S} {V} {T} l₁ l₂ l₃ (impl₁₁ , impl₁₂) (impl₂₁ , impl₂₂) (P-eq , Q-eq , get-eq , put-eq)
  = P-eq
  , (λ {_} {_} → refl)
  , (λ {s} → cong (get l₃) (get-eq {s}))
  , λ {s} {v} → put-eq′ s v
  where
    put-eq′ : (s : S) (v : T) →
              Q l₃ (get l₃ (get l₁ s)) v →
              put l₁ s (put l₃ (get l₁ s) v) ≡ put l₂ s (put l₃ (get l₂ s) v)
    put-eq′ s v q with (impl₂₁ ∘ backward-validity l₃) q
    ... | q-l₂ rewrite sym (get-eq {s}) | sym (Q-eq {get l₁ s} {put l₃ (get l₁ s) v})
      = put-eq {s} {put l₃ (get l₁ s) v} q-l₂


；-congʳ : ∀ {S V T : Set} →
           (l₁ : Lens S V) →
           (l₂ l₃ : Lens V T) →
           (cond₁ : compose-cond l₁ l₂) →
           (cond₂ : compose-cond l₁ l₃) →
           l₂ ≈ l₃ →
           l₁ ； l₂ [ cond₁ ]
           ≈
           l₁ ； l₃ [ cond₂ ]
；-congʳ {S} {V} {T} l₁ l₂ l₃ (impl₁₁ , impl₁₂) (impl₂₁ , impl₂₂) (P-eq , Q-eq , get-eq , put-eq)
  = (λ {_} {_} → refl)
  , Q-eq
  , (λ {s} → get-eq {get l₁ s})
  , λ {s} {v} q → cong (put l₁ s) (put-eq {get l₁ s} {v} q)

；-cong : ∀ {S V T : Set} →
          (ℓ₁ ℓ₂ : Lens S V) →
          (ℓ₃ ℓ₄ : Lens V T) →
          (cond₁ : compose-cond ℓ₁ ℓ₃) →
          (cond₂ : compose-cond ℓ₂ ℓ₄) →
          ℓ₁ ≈ ℓ₂ →
          ℓ₃ ≈ ℓ₄ →
          ℓ₁ ； ℓ₃ [ cond₁ ] ≈ ℓ₂ ； ℓ₄ [ cond₂ ]
；-cong ℓ₁ ℓ₂ ℓ₃ ℓ₄ cond₁ cond₂ ℓ₁≈ℓ₂ ℓ₃≈ℓ₄
  = ≈-trans (ℓ₁ ； ℓ₃ [ cond₁ ])
            (ℓ₂ ； ℓ₃ [ induced-cond₁ ])
            (ℓ₂ ； ℓ₄ [ cond₂ ])
            (；-congˡ ℓ₁ ℓ₂ ℓ₃ cond₁ induced-cond₁ ℓ₁≈ℓ₂)
            (；-congʳ ℓ₂ ℓ₃ ℓ₄ induced-cond₁ cond₂ ℓ₃≈ℓ₄)
  where
    induced-cond₁′ : ℓ₁ ≈ ℓ₂ → compose-cond ℓ₁ ℓ₃ → compose-cond ℓ₂ ℓ₃
    induced-cond₁′ ℓ₁≈ℓ₂ (impl , impl′) with ℓ₁≈ℓ₂
    ... | (P-eq , Q-eq , _ , _) = (λ p → transport′ Q-eq (impl p)) , λ q → impl′ (transport′ (sym Q-eq) q)
    induced-cond₁ = induced-cond₁′ ℓ₁≈ℓ₂ cond₁


；-congᵐ : ∀ {S V T R : Set} →
             (ℓ₁ : Lens S V) →
             (ℓ₂ ℓ₃ : Lens V T) →
             (ℓ₄ : Lens T R) →
             (cond₁ : compose-cond ℓ₁ ℓ₂) →
             (cond₂ : compose-cond ℓ₂ ℓ₄) →
             (cond₃ : compose-cond ℓ₁ ℓ₃) →
             (cond₄ : compose-cond ℓ₃ ℓ₄) →
             ℓ₂ ≈ ℓ₃ →
             ℓ₁ ； ℓ₂ [ cond₁ ] ； ℓ₄ [ cond₂ ]
             ≈
             ℓ₁ ； ℓ₃ [ cond₃ ] ； ℓ₄ [ cond₄ ]
；-congᵐ ℓ₁ ℓ₂ ℓ₃ ℓ₄ cond₁ cond₂ cond₃ cond₄ ℓ₂≈ℓ₃
  = ；-cong (ℓ₁ ； ℓ₂ [ cond₁ ])
            (ℓ₁ ； ℓ₃ [ cond₃ ])
            ℓ₄ ℓ₄
            cond₂ cond₄
            (；-congʳ ℓ₁ ℓ₂ ℓ₃ cond₁ cond₃ ℓ₂≈ℓ₃)
            (≈-refl ℓ₄)


；-assoc : ∀ {S V T R : Set} →
           (ℓ₁ : Lens S V) → (ℓ₂ : Lens V T) → (ℓ₃ : Lens T R) →
           (cond₁ : compose-cond ℓ₁ ℓ₂) → (cond₂ : compose-cond ℓ₂ ℓ₃) →
           (ℓ₁ ； ℓ₂ [ cond₁ ]) ； ℓ₃ [ cond₂ ]
           ≈
           ℓ₁ ； (ℓ₂ ； ℓ₃ [ cond₂ ]) [ cond₁ ]
；-assoc ℓ₁ ℓ₂ ℓ₃ (impl₁ , impl₁′) (impl₂ , impl₂′)
  = refl
  , refl
  , refl
  , λ {s} {v} _ → put-equal s v
  where
    put-equal : ∀ s v →
                  put ((ℓ₁ ； ℓ₂ [ impl₁ , impl₁′ ]) ； ℓ₃ [ impl₂ , impl₂′ ]) s v
                ≡
                  put (ℓ₁ ； ℓ₂ ； ℓ₃ [ impl₂ , impl₂′ ] [ impl₁ , impl₁′ ]) s v
    put-equal s v = refl


；-assoc₄ : ∀ {S V T R W : Set} →
            (ℓ₁ : Lens S V) → (ℓ₂ : Lens V T) → (ℓ₃ : Lens T R) → (ℓ₄ : Lens R W) →
            (cond₁ : compose-cond ℓ₁ ℓ₂) → (cond₂ : compose-cond ℓ₂ ℓ₃) → (cond₃ : compose-cond ℓ₃ ℓ₄) →
            ℓ₁ ； ℓ₂ [ cond₁ ] ； ℓ₃ [ cond₂ ] ； ℓ₄ [ cond₃ ]
            ≈
            ℓ₁ ； (ℓ₂ ； ℓ₃ [ cond₂ ] ； ℓ₄ [ cond₃ ]) [ cond₁ ]
；-assoc₄ ℓ₁ ℓ₂ ℓ₃ ℓ₄ cond₁ cond₂ cond₃
  = ≈-trans
      (ℓ₁ ； ℓ₂ [ cond₁ ] ； ℓ₃ [ cond₂ ] ； ℓ₄ [ cond₃ ])
      (ℓ₁ ； (ℓ₂ ； ℓ₃ [ cond₂ ]) [ cond₁ ] ； ℓ₄ [ cond₃ ])
      (ℓ₁ ； (ℓ₂ ； ℓ₃ [ cond₂ ] ； ℓ₄ [ cond₃ ]) [ cond₁ ])
      (；-congˡ (ℓ₁ ； ℓ₂ [ cond₁ ] ； ℓ₃ [ cond₂ ])
                (ℓ₁ ； (ℓ₂ ； ℓ₃ [ cond₂ ]) [ cond₁ ])
                ℓ₄
                cond₃
                cond₃
                (；-assoc ℓ₁ ℓ₂ ℓ₃ cond₁ cond₂))
      (；-assoc ℓ₁ (ℓ₂ ； ℓ₃ [ cond₂ ]) ℓ₄ cond₁ cond₃)
           
           



module ≈-Reasoning {S V : Set} where

  infix 3 _∎ˡ
  infixr 2 _≈⟨⟩_ _≈⟨_⟩_
  infix 1 beginˡ_

  beginˡ_ : ∀ {l₁ l₂ : Lens S V} → l₁ ≈ l₂ → l₁ ≈ l₂
  beginˡ_ l₁≈l₂ = l₁≈l₂

  _≈⟨⟩_ : ∀ (l₁ {l₂} : Lens S V) → l₁ ≈ l₂ → l₁ ≈ l₂
  _ ≈⟨⟩ l₁≈l₂ = l₁≈l₂

  _≈⟨_⟩_ : ∀ (l₁ {l₂ l₃} : Lens S V) → l₁ ≈ l₂ → l₂ ≈ l₃ → l₁ ≈ l₃
  _≈⟨_⟩_ l₁ {l₂} {l₃}  l₁≈l₂ l₂≈l₃ = ≈-trans l₁ l₂ l₃  l₁≈l₂ l₂≈l₃

  _∎ˡ : ∀ (l : Lens S V) → l ≈ l
  l ∎ˡ = ≈-refl l
  


_hasConditions_and_ : ∀ {A : Set} {B : Set} →
                      Lens A B → (P : A → A → Set) → (Q : B → B → Set) →
                      Set₁
l hasConditions P and Q = Lens.P l ≡ P × Lens.Q l ≡ Q


get-put-law-from-lens-data : ∀ {A : Set} {B : Set} →
                             {P : A → A → Set} → {Q : B → B → Set} →
                             (l-data : Σ (Lens A B) λ l → l hasConditions P and Q) →
                             ∀ {a : A} → P a a → put (proj₁ l-data) a (get (proj₁ l-data) a) ≡ a
get-put-law-from-lens-data {A} {B} {P} {Q} (l , P-eq , Q-eq) {a} q
  = conditioned-get-put l {a} ((transport′ (cong (λ pred → pred a a) (sym P-eq)) q) )

put-get-law-from-lens-data : ∀ {A : Set} {B : Set} →
                             {P : A → A → Set} → {Q : B → B → Set} →
                             (l-data : Σ (Lens A B) λ l  → l hasConditions P and Q) →
                             ∀ {a : A} {b : B} → Q (get (proj₁ l-data) a) b → get (proj₁ l-data) (put (proj₁ l-data) a b) ≡ b
put-get-law-from-lens-data {A} {B} {P} {Q} (l , P-eq , Q-eq) {a} {b} q
  = conditioned-put-get l {a} {b} (transport′ (cong (λ pred → pred (get l a) b) (sym Q-eq)) q)

change-transformation-from-lens-data
  : ∀ {A : Set} {B : Set} →
    {P : A → A → Set} → {Q : B → B → Set} →
    (l-data : Σ (Lens A B)
    λ l → l hasConditions P and Q) →
    ∀ {a : A} {b : B} → Q (get (proj₁ l-data) a) b → P a (put (proj₁ l-data) a b)
change-transformation-from-lens-data  {A} {B} {P} {Q} (l , P-eq , Q-eq) {a} {b} q
  = transport′ (cong (λ pred → pred a (put l a b)) P-eq)
               (backward-validity l {a} {b} (transport′ (sym (cong (λ pred → pred (get l a) b) Q-eq)) q))

forward-validity-from-lens-data
  : ∀ {A : Set} {B : Set} →
    {P : A → A → Set} → {Q : B → B → Set} →
    (l-data : Σ (Lens A B)
    λ l → l hasConditions P and Q) →
    ∀ {a : A} → P a a → Q (get (proj₁ l-data) a) (get (proj₁ l-data) a)
forward-validity-from-lens-data {A} {B} {P} {Q} (l , P-eq , Q-eq) {a}  p
  = transport′ (cong (λ pred → pred (get l a) (get l a)) Q-eq)
               (forward-validity l {a}  (transport′ (cong (λ pred → pred a a) (sym P-eq)) p))
 
