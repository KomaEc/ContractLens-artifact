module Core where

open import Agda.Primitive
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂; cong-app; subst)
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
open import Util using (η-⊤; transport′; funext; funext'; case_of_)
open import Data.Maybe.Base using (just; nothing; maybe)
-- open import Data.Integer as ℤ renaming (suc to zsuc)
open import Induction.WellFounded
open import Data.Nat.Induction
import Data.Integer as ℤ
open import Data.IntegerOmega.Base as ℤω
open import Data.IntegerOmega.Properties
open import Data.Bool
open import Lens
open Lens.Lens
open import UniCombinatorsAndProperties

private
  variable
    ℓ ℓ′ : Level



--------------------------------------------------
--| some useful properties                     --|
--------------------------------------------------






data ConsecutivePairs {A : Set} (R : A → A → Set) (a₀ : A) : List A  → Set where
  [] : ConsecutivePairs R a₀ []
  _∷_ : ∀ {a as} → R a₀ a → ConsecutivePairs R a as → ConsecutivePairs R a₀ (a ∷ as)

module ConsecutivePairsProperties where


  cp-true : ∀ {A : Set} →
               ∀ {a₀ : A} {as} →
               ConsecutivePairs (λ _ _ → ⊤) a₀ as
  cp-true {A} {a₀} {[]} = []
  cp-true {A} {a₀} {(x ∷ as)} = tt ∷ cp-true {A} {x} {as}

  cp-snoc : ∀ {A : Set} (R : A → A → Set) →
            (a₀ : A) → (as : List A) (a a′ : A) →
            ConsecutivePairs R a₀ (as ++ a ∷ []) →
            R a a′ →
            ConsecutivePairs R a₀ (as ++ a ∷ a′ ∷ [])
  cp-snoc R a₀ [] a a′ (Ra₀a ∷ []) Raa′ = Ra₀a ∷ Raa′ ∷ []
  cp-snoc R a₀ (x ∷ as) a a′ (Ra₀x ∷ cp-R) Raa′ = Ra₀x ∷ cp-snoc R x as a a′ cp-R Raa′

  cp-unsnoc : ∀ {A : Set} (R : A → A → Set) →
              (a₀ : A) → (as : List A) (a a′ : A) →
              ConsecutivePairs R a₀ (as ++ a ∷ a′ ∷ []) →
              ConsecutivePairs R a₀ (as ++ a ∷ []) × R a a′
  cp-unsnoc R a₀ [] a a′ (Ra₀a ∷ (Raa′ ∷ [])) = Ra₀a ∷ [] , Raa′
  cp-unsnoc R a₀ (x ∷ as) a a′ (Ra₀x ∷ cp-R) with cp-unsnoc R x as a a′ cp-R
  ... | cp-R′ , Raa′ =  Ra₀x ∷ cp-R′ , Raa′


data Pointwise {A : Set} {B : Set} (R : A → B → Set) : List A → List B → Set where
  [] : Pointwise R [] []
  _∷_ : ∀ {x xs y ys} → R x y → Pointwise R xs ys → Pointwise R (x ∷ xs) (y ∷ ys)

module CommonConditions where

  true-cond : {A : Set} → A → A → Set
  true-cond = λ _ _ → ⊤

  eq-length : {A : Set} → List A → List A → Set
  eq-length = λ xs xs′ → length xs ≡ length xs′

  map-dep-cond : {A : Set} (P̃ : A → A → Set) → A × A → A × A → Set
  map-dep-cond P̃ (_ , a) (a′ , a′′) = P̃ a a′ × a ≡ a′′

  data map-dep-cond′ {A : Set} (P̃ : A → A → Set) : A × A → A × A → Set where
    map-dep-cond′-ok : ∀ {a₁ a a′} → P̃ a a′ → map-dep-cond′ P̃ (a₁ , a) (a′ , a)

  scanl-cond : {A : Set} {B : Set} → Maybe (A × B) × B → Maybe (A × B) × B → Set
  scanl-cond (_ , b) (just (_ , b′′) , b′) = b ≡ b′ × b ≡ b′′
  scanl-cond (_ , _) (nothing , _) = ⊥

  data scan-cond′ {A : Set} {B : Set} : Maybe (A × B) × B → Maybe (A × B) × B → Set where
    scan-cond′-ok : ∀ {m b a} → scan-cond′ (m , b) (just (a , b) , b)

  foldl-cond : {A : Set} {B : Set} → Maybe (A × B) × B → Maybe (A × B) × B → Set
  foldl-cond = scanl-cond

  -- as ≡ init as′
  is-init : {A : Set} → List A → List A → Set
  is-init as as′ = ∃[ a ] (as ++ (a ∷ []) ≡ as′)

  data is-init′ {A : Set} : List A → List A → Set where
    is-init′-ok : ∀ {as a} → is-init′ as (as ++ (a ∷ []))

  -- tail as ≡ as′
  is-tail : {A : Set} → List A → List A → Set
  is-tail as as′ = ∃[ a ] (as ≡ a ∷ as′)

  is-mapinit∘init : {A : Set} → (∃[ xss ] (∃[ xs ] (tails {A} xs ≡ xss))) →
                                (∃[ xss ] (∃[ xs ] (tails {A} xs ≡ xss))) → Set
  is-mapinit∘init (ass , _) (ass′ , _)
    = ∃[ ass′′ ] (∃[ as′ ] (ass′′ ++ as′ ∷ [] ≡ ass′ × Pointwise is-init ass ass′′))

  data tails-list {A : Set} : List (List A) → Set where
    tails-list-ok : ∀ {xs} → tails-list (tails xs)

  is-mapminus-rear : List ℤω → List ℤω → Set
  is-mapminus-rear as as′ = ∃[ b ] (as′ ≡ map (ℤω._+_ b) as ++ b ∷ [])

  keep-form
    : {A B : Set} (b₀ : B) → Maybe (A × B) → Maybe (A × B) → Set
  keep-form b₀ (just (a , b)) (just (a′ , b′)) = b ≡ b₀ → b′ ≡ b₀
  keep-form _ (just (a , b)) nothing = ⊥
  keep-form _ nothing (just (a′ , b′)) = ⊤
  keep-form _ nothing nothing = ⊤

  data lift {A B : Set} (P : A → A → Set) (Q : B → B → Set) : Maybe (A × B) → Maybe (A × B) → Set where
    nothing : lift P Q nothing nothing
    just : ∀ {x y x′ y′} → P x x′ → Q y y′ → lift P Q (just (x , y)) (just (x′ , y′))

  licond : {A : Set} (P : A → A → Set) → List A → List A → Set
  licond P xs xs′ = length xs ≡ length xs′ × Pointwise P xs xs′
  filter-cond : {A : Set} →
                (P : A → A → Set) →
                (p : A → Bool) →
                List A → List A → Set
  filter-cond P p = licond λ x x′ → P x x′ × {- p x ≡ true × -} p x′ ≡ true

module CommonConditionsProperties {A : Set}  where
  open CommonConditions

  tails⇒cp-is-tail : ∀ (xs : List A) →
                     ConsecutivePairs (flip is-tail) [] (reverse (tails xs))
  tails⇒cp-is-tail [] = []
  tails⇒cp-is-tail (x ∷ xs) with tails-cons x xs | tails⇒cp-is-tail xs
  ... | eq | rec with tails xs
  tails⇒cp-is-tail (x ∷ .[]) | refl | rec | [] = (x , refl) ∷ []
  ... | xs′ ∷ xss with reverse ((x ∷ xs′) ∷ xs′ ∷ xss) | reverse-cons≡snoc (x ∷ xs′) (xs′ ∷ xss)
  ... | .(reverse (xs′ ∷ xss) ++ (x ∷ xs′) ∷ []) | refl with reverse (xs′ ∷ xss) | reverse-cons≡snoc xs′ xss
  ... | .(reverse xss ++ xs′ ∷ []) | refl with ConsecutivePairsProperties.cp-snoc (flip is-tail) [] (reverse xss) xs′ (x ∷ xs′) rec (x , refl)
  ... | ans with (reverse xss ++ xs′ ∷ []) ++ (x ∷ xs′) ∷ [] | Data.List.Properties.++-assoc (reverse xss) (xs′ ∷ []) ((x ∷ xs′) ∷ [])
  ... | .(reverse xss ++ xs′ ∷ (x ∷ xs′) ∷ []) | refl = ans

  cp-is-tail-uncons : ∀ (xs₀ xs xs′ : List A) (xss : List (List A)) →
                      ConsecutivePairs (flip is-tail) xs₀ (reverse (xs ∷ xs′ ∷ xss)) →
                      ConsecutivePairs (flip is-tail) xs₀ (reverse (xs′ ∷ xss)) × is-tail xs xs′
  cp-is-tail-uncons xs₀ xs xs′ xss cp-is-tail with reverse (xs ∷ xs′ ∷ xss) | reverse-cons≡snoc xs (xs′ ∷ xss)
  ... | .(reverse (xs′ ∷ xss) ++ xs ∷ []) | refl with  reverse (xs′ ∷ xss) | reverse-cons≡snoc xs′ xss
  ... | .(reverse xss ++ xs′ ∷ []) | refl with (reverse xss ++ xs′ ∷ []) ++ xs ∷ [] | Data.List.Properties.++-assoc (reverse xss) (xs′ ∷ []) (xs ∷ [])
  ... | .(reverse xss ++ xs′ ∷ xs ∷ []) | refl  with ConsecutivePairsProperties.cp-unsnoc (flip is-tail) xs₀ (reverse xss) xs′ xs cp-is-tail
  cp-is-tail-uncons xs₀ .(x ∷ xs′) xs′ xss cp-is-tail
    | .(foldl _ (xs′ ∷ []) xss ++ (x ∷ xs′) ∷ [])
    | refl | .(foldl _ [] xss ++ xs′ ∷ []) | refl | .(foldl _ [] xss ++ xs′ ∷ (x ∷ xs′) ∷ []) | refl
    | cp-is-tail′ , x , refl = cp-is-tail′ ,  x , refl


  cp-is-tail-cons⇒tails : ∀ (xs₀ xs : List A) (xss : List (List A)) →
                              ConsecutivePairs (flip is-tail) xs₀ (reverse (xs ∷ xss)) →
                              xs ∷ xss ++ tails xs₀ ≡ tails xs
  cp-is-tail-cons⇒tails xs₀ .(x ∷ xs₀) [] ((x , refl) ∷ cp-is-tail) = sym (tails-cons x xs₀)
  cp-is-tail-cons⇒tails xs₀ xs (xs′ ∷ xss) cp-is-tail with cp-is-tail-uncons xs₀ xs xs′ xss cp-is-tail
  cp-is-tail-cons⇒tails xs₀ .(x ∷ xs′) (xs′ ∷ xss) cp-is-tail | cp-is-tail′ , x , refl
    rewrite cp-is-tail-cons⇒tails xs₀ xs′ xss cp-is-tail′ = sym (tails-cons x xs′)

  mapsnoc⇒ptwise-is-init : ∀ (xss : List (List A)) →
                           (a : A) →
                           Pointwise is-init xss (map (λ xs → xs ++ a ∷ []) xss)
  mapsnoc⇒ptwise-is-init [] a = []
  mapsnoc⇒ptwise-is-init (xs ∷ xss) a = (a , refl) ∷ mapsnoc⇒ptwise-is-init xss a


  ptwise-is-init-tail⇒is-init
    : ∀ (as as′ : List A) →
      (ass : List (List A)) →
      is-init ass (tails as′) →
      Pointwise is-init (tails as) ass →
      is-init as as′
  ptwise-is-init-tail⇒is-init [] (x ∷ []) .[] (as′′ , eq₁) [] = x , refl
  ptwise-is-init-tail⇒is-init [] (x ∷ x₁ ∷ as′) .[] (as′′ , eq₁) []
    with trans (trans eq₁ (tails-cons x (x₁ ∷ as′))) (cong (_∷_ (x ∷ x₁ ∷ as′)) (tails-cons x₁ as′))
  ... | ()
  ptwise-is-init-tail⇒is-init (a ∷ as) as′ ass (as′′ , eq₁) ptw with tails (a ∷ as) | tails-cons a as
  ptwise-is-init-tail⇒is-init (a ∷ as) (a′ ∷ as′) (.(a ∷ as ++ a′′ ∷ []) ∷ ass) (as′′ , eq₁) ((a′′ , refl) ∷ ptw)
    | .((a ∷ as) ∷ scanr _∷_ [] as) | refl
    = a′′ , tails-unique (a ∷ as ++ a′′ ∷ []) (ass ++ as′′ ∷ []) (a′ ∷ as′) eq₁

  map-ptwise : ∀ {A B : Set} →
               (R₁ R₂ : A → B → Set) →
               (∀ {x} {y} → R₁ x y → R₂ x y) →
               ∀ {xs} {ys} → Pointwise R₁ xs ys → Pointwise R₂ xs ys
  map-ptwise R₁ R₂ f [] = []
  map-ptwise R₁ R₂ f (x ∷ ps) = f x ∷ map-ptwise R₁ R₂ f ps
















---------------------------------------------------------
--| combinator bxmap-depl                             --|
--| bidirectional map with inner dependency relation  --|
--| congruence law and fusion law                     --|
---------------------------------------------------------

module Map-Helper {S V : Set} (l : Lens (S × S) (V × V)) where
  g-aux : S → List S → List V
  g-aux a₀ [] = []
  g-aux a₀ (a ∷ as) = proj₁ (get l (a , a₀)) ∷ g-aux a as

  g-aux-length : ∀ {a₀} {as} →
                 length (g-aux a₀ as) ≡ length as
  g-aux-length {a₀} {[]} = refl
  g-aux-length {a₀} {x ∷ as} = cong suc (g-aux-length {x} {as})

  g-aux-independent : ∀ {a a′} {as} {f-data : (Σ (S → V) λ f →  (∀ {a a′} → get l (a , a′) ≡ (f a , f a′)))} →
                      g-aux a as ≡ g-aux a′ as
  g-aux-independent {a} {a′} {[]} {_} = refl
  g-aux-independent {a} {a′} {x ∷ as} {f , f-eq} = cong₂ _∷_ (trans (cong proj₁ f-eq) (sym (cong proj₁ f-eq))) refl

  g-aux-computation : ∀ a as →
                      (f-data  : (Σ (S → V) λ f →  (∀ {a a′} → get l (a , a′) ≡ (f a , f a′)))) →
                      g-aux a as ≡ map (proj₁ f-data) as
  g-aux-computation a [] (f , f-eq) = refl
  g-aux-computation a (x ∷ as) (f , f-eq) = cong₂ _∷_ (cong proj₁ f-eq) (g-aux-computation x as (f , f-eq))

  p-aux : S → V → List S → List V → List S
  p-aux a₀ b₀ [] [] = []
  p-aux a₀ b₀ [] (x ∷ bs) = [] -- failed branch
  p-aux a₀ b₀ (x ∷ as) [] = [] -- failed branch
  p-aux a₀ b₀ (a ∷ as) (b ∷ bs) = proj₁ (put l (a , a₀) (b , b₀)) ∷ p-aux (proj₁ (put l (a , a₀) (b , b₀))) b as bs



bmapl-component : ∀ {S V : Set} → {P : S → S → Set} → {Q : V → V → Set} →
  (ℓ-data : (a : S) → (Σ (Lens S V) λ ℓ → ℓ hasConditions (λ _ a′ → P a a′) and λ _ b′ → Q (get ℓ a) b′)) →
  (Σ (S → V) λ f → ∀ (a a′ : S) → get (proj₁ (ℓ-data a)) a′ ≡ f a′) →
  (Σ (Σ (Lens (S × S) (V × V))
                       (λ l → l hasConditions (CommonConditions.map-dep-cond {S} P)
                               and            CommonConditions.map-dep-cond {V} Q)) λ ℓ-data → (Σ (S → V) λ f →  (∀ {a a′} → get (proj₁ ℓ-data) (a , a′) ≡ (f a , f a′))))
                      
bmapl-component {S} {V} {P̂} {Q̂} ℓ-data (f , f-eq) = (l , (refl , refl)) , f , refl
  where
    l : Lens (S × S) (V × V)
    get l = λ (a , a′) → f a , f a′
    put l = λ (a , a′) (b , b′) → (put (proj₁ (ℓ-data a′)) a b , a′)
    P l = CommonConditions.map-dep-cond {S} P̂
    Q l = CommonConditions.map-dep-cond {V} Q̂
    backward-validity l {a , a′} {b , b′} (view-cond₁ , refl) with proj₂ (ℓ-data a′)
    ... | source-cond-eq , view-cond-eq with backward-validity (proj₁ (ℓ-data a′)) {a} {b} (transport′ (cong (λ x → Q (proj₁ (ℓ-data a′)) x b) (sym (f-eq a′ a))) (transport′ (cong (λ pred → pred (f a) b) (sym view-cond-eq)) (transport′ ((cong (λ x → Q̂ x b)  (sym (f-eq a′ a′)))) view-cond₁)))
    ... | ℓ-backward-validity = transport′ (cong (λ pred → pred a (put (proj₁ (ℓ-data a′)) a b)) source-cond-eq) ℓ-backward-validity , refl
    forward-validity l {a , a′} (source-cond₁ , refl) with proj₂ (ℓ-data a′)
    ... | source-cond-eq , view-cond-eq with forward-validity (proj₁ (ℓ-data a′)) {a} (transport′ (cong (λ pred → pred a a) (sym source-cond-eq) ) source-cond₁)
    ... | ℓ-forward-validity rewrite f-eq a′ a | cong (λ pred → pred (f a) (f a)) view-cond-eq | f-eq a′ a′ = transport′ refl ℓ-forward-validity , refl
    conditioned-get-put l {a , a′} (source-cond₁ , refl) with proj₂ (ℓ-data a′)
    ... | source-cond-eq , _ with conditioned-get-put (proj₁ (ℓ-data a′)) {a}
    ... | cgp rewrite f-eq a′ a | cong (λ pred → pred a a) source-cond-eq = cong₂ _,_ (cgp source-cond₁) refl
    conditioned-put-get l {a , a′} {b , b′} (view-cond₁ , refl) with proj₂ (ℓ-data a′)
    ... | _ , view-cond-eq with conditioned-put-get (proj₁ (ℓ-data a′)) {a} {b}
    ... | cpg rewrite f-eq a′ a | cong (λ pred → pred (f a) b) view-cond-eq | f-eq a′ (put (proj₁ (ℓ-data a′)) a b) | f-eq a′ a′ = cong₂ _,_ (cpg view-cond₁) refl



bmapl-component-reverse : ∀ {S V : Set} → {P̂ : S → S → Set} → {Q̂ : V → V → Set} →
                          (ℓ-data : Σ (Lens (S × S) (V × V)) λ ℓ → ℓ hasConditions CommonConditions.map-dep-cond {S} P̂
                                                                     and CommonConditions.map-dep-cond {V} Q̂) →
                          (Σ (S → V) λ f →  (∀ {a a′} → get (proj₁ ℓ-data) (a , a′) ≡ (f a , f a′))) → 
                          Σ ((a : S) → Σ (Lens S V) λ ℓ → ℓ hasConditions (λ _ a′ → P̂ a a′) and λ _ b′ → Q̂ (get ℓ a) b′) λ ℓ-data → (Σ (S → V) λ f → ∀ (a a′ : S) → get (proj₁ (ℓ-data a)) a′ ≡ f a′)
bmapl-component-reverse {S} {V} {P̂} {Q̂} ℓ-data (f , f-eq) = (λ a → l a , refl , refl) , f , λ _ _ → refl
  where
    l : S → Lens S V
    get (l a′) = f
    put (l a′) = λ a b → proj₁ (put (proj₁ ℓ-data) (a , a′) (b , get (l a′) a′))
    P (l a′) = λ _ → P̂ a′
    Q (l a′) = λ _ → Q̂ (get (l a′) a′)
    backward-validity (l a′) {a} {b} view-cond with change-transformation-from-lens-data ℓ-data {a , a′} {b , get (l a′) a′}
    ... | ℓ-backward-validity rewrite cong proj₁ (f-eq {a} {a′}) | cong proj₂ (f-eq {a} {a′}) = proj₁ (ℓ-backward-validity (view-cond , refl))
    forward-validity (l a′) {a} source-cond with forward-validity-from-lens-data ℓ-data {a , a′}
    ... | ℓ-forward-validity rewrite cong proj₁ (f-eq {a} {a′}) | cong proj₂ (f-eq {a} {a′}) = proj₁ (ℓ-forward-validity (source-cond , refl))
    conditioned-get-put (l a′) {a} source-cond with get-put-law-from-lens-data ℓ-data {a , a′}
    ... | cgp rewrite f-eq {a} {a′} = cong proj₁ (cgp (source-cond , refl))
    conditioned-put-get (l a′) {a} {b} view-cond with put-get-law-from-lens-data ℓ-data {a , a′} {b , get (l a′) a′}
    ... | cpg with put (proj₁ ℓ-data) (a , a′) (b , f a′)
    ... | (a′′ , a′′′) rewrite f-eq {a′′} {a′′′} | f-eq {a} {a′} = cong proj₁ (cpg (view-cond , refl))
  

bmapl-component-right-inverse : ∀ {S V : Set} → {P : S → S → Set} → {Q : V → V → Set} →
                                (ℓ-data : (a : S) → (Σ (Lens S V) λ ℓ → ℓ hasConditions (λ _ a′ → P a a′) and λ _ b′ → Q (get ℓ a) b′)) →
                                (f-data : Σ (S → V) λ f → ∀ (a a′ : S) → get (proj₁ (ℓ-data a)) a′ ≡ f a′) → ∀ {a′} → proj₁ (ℓ-data a′) ≈ proj₁ (proj₁ (Data.Product.uncurry bmapl-component-reverse (bmapl-component {P = P} {Q = Q}  ℓ-data f-data)) a′) 
bmapl-component-right-inverse {S} {V} {P} {Q} ℓ-data (f , f-eq) {a′} with proj₂ (ℓ-data a′)
... | source-cond-eq , view-cond-eq =
  (λ {s} {s′} → cong (λ pred → pred s s′) source-cond-eq) ,
  ((λ {v} {v′} → trans (cong (λ pred → pred v v′) view-cond-eq) (cong (λ v → Q v v′) (f-eq a′ a′)) ) ,
  ((λ {s} → f-eq a′ s) ,
  λ {s} {v} view-cond → refl))


bmapl-component-reverse-right-inverse : ∀ {S V : Set} → {P : S → S → Set} → {Q : V → V → Set} →
                                        (ℓ-data : Σ (Lens (S × S) (V × V)) λ ℓ → ℓ hasConditions CommonConditions.map-dep-cond {S} P
                                                                     and CommonConditions.map-dep-cond {V} Q) →
                                        (f-data : Σ (S → V) λ f →  (∀ {a a′} → get (proj₁ ℓ-data) (a , a′) ≡ (f a , f a′))) → 
                                        proj₁ ℓ-data ≈ proj₁ (proj₁ (Data.Product.uncurry (bmapl-component {P = P} {Q = Q}) (bmapl-component-reverse {P̂ = P} {Q̂ = Q} ℓ-data f-data)))
bmapl-component-reverse-right-inverse {S} {V} {P̂} {Q̂} ℓ-data (f , f-eq) with proj₂ ℓ-data
... | source-cond-eq , view-cond-eq =
  (λ {s} {s′} → cong (λ pred → pred s s′) source-cond-eq) ,
  (λ {v} {v′} → cong (λ pred → pred v v′) view-cond-eq) ,
  (λ {s} → f-eq {proj₁ s} {proj₂ s}) ,
  lemma 
  -- λ {s} {v} view-cond → {!transport′ (cong (λ pred → pred (get (proj₁ ℓ-data) s) v) view-cond-eq) view-cond!}
  where
    lemma : {s : Σ S (λ x → S)} {v : Σ V (λ x → V)} →
      Q (proj₁ ℓ-data) (get (proj₁ ℓ-data) s) v →
      put (proj₁ ℓ-data) s v ≡
      (proj₁ (put (proj₁ ℓ-data) s (proj₁ v , f (proj₂ s))) , proj₂ s)
    lemma {s , s′} {v , v′} view-cond with transport′ (cong (λ pred → pred (get (proj₁ ℓ-data) (s , s′)) (v , v′)) view-cond-eq) view-cond
    ... | cond , eq with change-transformation-from-lens-data ℓ-data (cond , eq)
    ... | cond′ , eq′ with trans (sym (cong proj₂ (f-eq {s} {s′}))) eq
    ... | refl with put (proj₁ ℓ-data ) (s , s′) (v , v′) | eq′
    ... | s′′ , .s′ | refl = refl


bxmap-depl : ∀ {S V : Set} →
            {P̃ : S → S → Set} →
            {Q̃ : V → V → Set} →
            (a₀ : S) →
            (l-data : Σ (Lens (S × S) (V × V))
                       λ l → l hasConditions (CommonConditions.map-dep-cond {S} P̃)
                               and            CommonConditions.map-dep-cond {V} Q̃) →
            (Σ (S → V) λ f →  (∀ {a a′} → get (proj₁ l-data) (a , a′) ≡ (f a , f a′))) →
            Lens (List S) (List V)
bxmap-depl {S} {V} {P̃} {Q̃} a₀ l-data (f , f-eq) -- NOTE: f-eq?
  = record
      { get = g
      ; put = p
      ; P = λ as′ as → ConsecutivePairs P̃ a₀ as × (length as′ ≡ length as)
      ; Q = λ bs′ bs → ConsecutivePairs Q̃ b₀ bs × (length bs′ ≡ length bs)
      ; backward-validity = λ {as} {bs} cond → prop₁ a₀ as bs cond
      ; forward-validity = λ { {as}  (cp-P̃ , eq-length) → (prop₂ a₀ as cp-P̃) , refl }
      ; conditioned-get-put = λ {as} → cgp a₀ as
      ; conditioned-put-get = λ {as} {bs} → cpg a₀ as bs
      }
  where
    l = proj₁ l-data
    l-conds = proj₂ l-data
    b₀ = f a₀
    f-eq′ : ∀ (aa : S × S) → proj₁ (get l aa) ≡ f (proj₁ aa)
    f-eq′ (a , a′) = cong proj₁ (f-eq {a} {a′})
    g-aux = Map-Helper.g-aux l
    p-aux = Map-Helper.p-aux l
    g-aux-length : ∀ {a₀ : S} {as : List S} →
                   length (g-aux a₀ as) ≡ length as
    g-aux-length {as = []} = refl
    g-aux-length {as = a ∷ as} = cong suc (g-aux-length {as = as})
    g : List S → List V
    g = g-aux a₀
    p : List S → List V → List S
    p = p-aux a₀ b₀
    cgp : (a₀ : S) (as : List S) →
          ConsecutivePairs P̃ a₀ as × length as ≡ length as → p-aux a₀ (f a₀) as (g-aux a₀ as) ≡ as
    cgp a₀ [] ([] , refl) = refl
    cgp a₀ (a ∷ as) ((P̃a₀a ∷ cp-P̃) , refl)
      rewrite cong proj₁ (f-eq {a} {a₀}) | sym (f-eq {a} {a₀}) | cong proj₁ (get-put-law-from-lens-data l-data {a , a₀} (P̃a₀a , refl))
      = cong₂ _∷_ refl (cgp a as (cp-P̃ , refl))
    cpg : (a₀ : S) (as : List S) (bs : List V) →
          ConsecutivePairs Q̃ (f a₀) bs × length (g-aux a₀ as) ≡ length bs → g-aux a₀ (p-aux a₀ (f a₀) as bs) ≡ bs
    cpg a₀ [] [] ([] , refl) = refl
    cpg a₀ (a ∷ as) (b ∷ bs) ((Q̃b₀b ∷ cp-Q̃) , length-eq)
      with put-get-law-from-lens-data l-data {a , a₀} {b , f a₀} | change-transformation-from-lens-data l-data {a , a₀} {b , f a₀}
    ... | pg-eq | change-transformation-eq  with get l (a , a₀) | f-eq {a} {a₀} 
    ... | .(f a , f a₀) | refl 
      = cong₂ _∷_
              (begin
                 proj₁ (get l (proj₁ (put l (a , a₀) (b , f a₀)) , a₀))
               ≡⟨ cong (λ x → proj₁ (get l (proj₁ (put l (a , a₀) (b , f a₀)) , x))) (proj₂ (change-transformation-eq (Q̃b₀b , refl))) ⟩
                 proj₁ (get l (proj₁ (put l (a , a₀) (b , f a₀)) , proj₂ (put l (a , a₀) (b , f a₀))))
               ≡⟨⟩
                 proj₁ (get l (put l (a , a₀) (b , f a₀)))
               ≡⟨ cong proj₁ (pg-eq (Q̃b₀b , refl)) ⟩
                 b
               ∎)
               (trans (cong (λ b′ →  g-aux (proj₁ (put (proj₁ l-data) (a , a₀) (b , f a₀)))
                      (p-aux (proj₁ (put (proj₁ l-data) (a , a₀) (b , f a₀))) b′ as bs))
                      (trans (cong proj₁ (sym (pg-eq (Q̃b₀b , refl)))) (f-eq′ (put l (a , a₀) (b , f a₀)))))
                      (cpg (proj₁ (put l (a , a₀) (b , f a₀))) as bs
                           (transport′
                             (cong (λ b → ConsecutivePairs Q̃ b bs)
                               (trans (cong proj₁ (sym (pg-eq (Q̃b₀b , refl)))) (f-eq′ (put l (a , a₀) (b , f a₀))))) cp-Q̃
                               , trans (trans (g-aux-length {proj₁ (put l (a , a₀) (b , f a₀))} {as}) (sym (g-aux-length {a} {as})))
                                                            (suc-injective length-eq))))
    prop₁ : (a₀ : S) (as : List S) (bs : List V) →
            ConsecutivePairs Q̃ (f a₀) bs × length (g-aux a₀ as) ≡ length bs →
            ConsecutivePairs P̃ a₀ (p-aux a₀ (f a₀) as bs) × length as ≡ length (p-aux a₀ (f a₀) as bs)
    prop₁ a₀ [] [] ([] , refl) = [] , refl
    prop₁ a₀ (a ∷ as) (b ∷ bs) ((Q̃b₀b ∷ cp-Q̃) , length-eq)
      with change-transformation-from-lens-data l-data {a , a₀} {b , f a₀}
                                                (transport′ (cong (λ b′ → Q̃ b′ b)
                                                            (sym (cong proj₂ (f-eq {a} {a₀})))) Q̃b₀b , cong proj₂ (f-eq {a} {a₀}))
    ... | (p , eq) with put-get-law-from-lens-data l-data {a , a₀} {b , f a₀}
    ... | pg-eq with get l (a , a₀) | f-eq {a} {a₀}
    ... | .(f a , f a₀) | refl
      with prop₁ (proj₁ (put (proj₁ l-data) (a , a₀) (b , f a₀))) as bs
                 (transport′ (cong (λ b → ConsecutivePairs Q̃ b bs)
                             ((trans (cong proj₁ (sym (pg-eq (Q̃b₀b , refl)))) (f-eq′ (put l (a , a₀) (b , f a₀)))))) cp-Q̃
                             , trans (trans (g-aux-length {(proj₁ (put l (a , a₀) (b , f a₀)))} {as}) (sym (g-aux-length {a} {as}))) (suc-injective length-eq))
    ... | (cp-P̃ , length-eq′)
      = p ∷ transport′ (cong (λ b′ → ConsecutivePairs P̃
                             (proj₁ (put (proj₁ l-data) (a , a₀) (b , f a₀)))
                             (p-aux (proj₁ (put (proj₁ l-data) (a , a₀) (b , f a₀))) b′ as bs) )
                             (sym (trans (cong proj₁ (sym (pg-eq (Q̃b₀b , refl)))) (f-eq′ (put l (a , a₀) (b , f a₀)))))) cp-P̃
                             , cong suc (trans length-eq′ (cong (λ b′ → length (p-aux (proj₁ (put (proj₁ l-data) (a , a₀) (b , f a₀))) b′ as bs))
                                                                ((sym (trans (cong proj₁ (sym (pg-eq (Q̃b₀b , refl))))
                                                                             (f-eq′ (put l (a , a₀) (b , f a₀)))))) ))

    prop₂ : (a₀ : S) (as : List S) →
            ConsecutivePairs P̃ a₀ as →
            ConsecutivePairs Q̃ (f a₀) (g-aux a₀ as)
    prop₂ a₀ [] [] = []
    prop₂ a₀ (a ∷ as) (P̃a₀a ∷ cp-P̃) with forward-validity-from-lens-data l-data {a , a₀} (P̃a₀a , refl)
    ... | (q , refl)
      = transport′ (cong (λ b → Q̃ b (proj₁ (get (proj₁ l-data) (a , a₀))))
                         (cong proj₂ (f-eq {a} {a₀})))
                   q ∷ transport′ (cong (λ b → ConsecutivePairs Q̃ b (g-aux a as)) (sym (cong proj₁ (f-eq {a} {a₀})))) (prop₂ a as cp-P̃)




bmapl : ∀ {S V : Set} →
         {P : S → S → Set} →
         {Q : V → V → Set} →
         (a₀ : S) →
         (ℓ-data : (a : S) → (Σ (Lens S V) λ ℓ → ℓ hasConditions (λ _ a′ → P a a′)
                                                  and            λ _ b′ → Q (get ℓ a) b′)) →
         (Σ (S → V) λ f → ∀ (a a′ : S) → get (proj₁ (ℓ-data a)) a′ ≡ f a′) → 
         Lens (List S) (List V)
bmapl {S} {V} {P} {Q} a₀ ℓ-data irrelevance = bxmap-depl {S} {V} {P} {Q} a₀ (proj₁ component) (proj₂ component)
  where
    component = bmapl-component {P = P} {Q = Q} ℓ-data irrelevance


；；-compose : ∀ {S V T : Set} →
        {P : S → S → Set} →
        {Q : V → V → Set} →
        {R : T → T → Set} →
        (ℓ₁-data : (a : S) → (Σ (Lens S V) λ ℓ → ℓ hasConditions (λ _ a′ → P a a′)
                                                  and            λ _ b′ → Q (get ℓ a) b′)) →
        (f₁-data : Σ (S → V) λ f → ∀ (a a′ : S) → get (proj₁ (ℓ₁-data a)) a′ ≡ f a′) →
        (ℓ₂-data : (b : V) → (Σ (Lens V T) λ ℓ → ℓ hasConditions (λ _ b′ → Q b b′)
                                                  and            λ _ c′ → R (get ℓ b) c′)) →
        (f₂-data : Σ (V → T) λ f → ∀ (b b′ : V) → get (proj₁ (ℓ₂-data b)) b′ ≡ f b′) → 
        Σ ((a : S) → Σ (Lens S T) λ ℓ → ℓ hasConditions (λ _ a′ → P a a′)
                                       and λ _ c′ → R (get ℓ a) c′)
          λ ℓ-data →  Σ (S → T) λ f → ∀ (a a′ : S) → get (proj₁ (ℓ-data a)) a′ ≡ f a′
；；-compose {S} {V} {T} {P̂} {Q̂} {R̂} ℓ₁-data f₁-data ℓ₂-data f₂-data with f₁-data | f₂-data
... | f₁ , f₁-eq | f₂ , f₂-eq = ℓ-data , f-data
  where ℓ-data : (a : S) → Σ (Lens S T) λ ℓ → ℓ hasConditions (λ _ a′ → P̂ a a′)
                                       and λ _ c′ → R̂ (get ℓ a) c′
        ℓ-data a with ℓ₁-data a
        ... | ℓ₁ , ℓ₁-source-cond-eq , ℓ₁-view-cond-eq  with ℓ₂-data (get ℓ₁ a)
        ... | ℓ₂ , ℓ₂-source-cond-eq , ℓ₂-view-cond-eq = ℓ₁ ； ℓ₂
          [ (λ {v} {v′} → transport′ (cong (λ pred → pred v v′) (trans ℓ₂-source-cond-eq (sym ℓ₁-view-cond-eq)))) ,
          (λ {s} {s′} → transport′ (cong (λ pred → pred s s′) (trans ℓ₁-view-cond-eq (sym ℓ₂-source-cond-eq)))) ] ,
          ℓ₁-source-cond-eq , ℓ₂-view-cond-eq
        lemma : (a a′ : S) → get (proj₁ (ℓ-data a)) a′ ≡ f₂ (f₁ a′)
        lemma a a′ with f₁-eq a
        ... | f₁-eq with ℓ₁-data a
        ... | ℓ₁ , _ with f₂-eq (get ℓ₁ a)
        ... | f₂-eq with ℓ₂-data (get ℓ₁ a)
        ... | ℓ₂ , _ = trans (f₂-eq (get ℓ₁ a′)) (cong f₂ (f₁-eq a′)) 
        f-data : Σ (S → T) (λ f → (a a′ : S) → get (proj₁ (ℓ-data a)) a′ ≡ f a′)
        f-data = f₂ ∘ f₁ , lemma




bmapl-component-homomorphism : ∀ {S V T : Set} →
                               {P : S → S → Set} →
                               {Q : V → V → Set} →
                               {R : T → T → Set} →
                               (ℓ₁-data : (a : S) → (Σ (Lens S V) λ ℓ → ℓ hasConditions (λ _ a′ → P a a′)
                                                                          and            λ _ b′ → Q (get ℓ a) b′)) →
                               (f₁-data : Σ (S → V) λ f → ∀ (a a′ : S) → get (proj₁ (ℓ₁-data a)) a′ ≡ f a′) →
                               (ℓ₂-data : (b : V) → (Σ (Lens V T) λ ℓ → ℓ hasConditions (λ _ b′ → Q b b′)
                                                                          and            λ _ c′ → R (get ℓ b) c′)) →
                               (f₂-data : Σ (V → T) λ f → ∀ (b b′ : V) → get (proj₁ (ℓ₂-data b)) b′ ≡ f b′) → 
                               proj₁ (proj₁ (Data.Product.uncurry (bmapl-component {P = P} {Q = R}) (；；-compose {P = P} {Q = Q} {R = R} ℓ₁-data f₁-data ℓ₂-data f₂-data))) ≈ (proj₁ (proj₁ (bmapl-component ℓ₁-data f₁-data)) ； (proj₁ (proj₁ (bmapl-component {Q = R} ℓ₂-data f₂-data))) [ (λ {v} {v′} → transport′ (cong (λ pred → pred v v′) (trans (proj₁ (proj₂ (proj₁ (bmapl-component {Q = R} ℓ₂-data f₂-data)))) (sym (proj₂ (proj₂ (proj₁ (bmapl-component ℓ₁-data f₁-data)))))))) , (λ {s} {s′} → transport′ (cong (λ pred → pred s s′ ) (trans (proj₂ (proj₂ (proj₁ (bmapl-component ℓ₁-data f₁-data)))) (sym (proj₁ (proj₂ (proj₁ (bmapl-component {Q = R} ℓ₂-data f₂-data)))))) )) ])
bmapl-component-homomorphism {S} {V} {T} {P̂} {Q̂} {R̂} ℓ₁-data f₁-data ℓ₂-data f₂-data with bmapl-component {Q = Q̂} ℓ₁-data f₁-data | bmapl-component {Q = R̂} ℓ₂-data f₂-data | f₁-data | f₂-data
... | ℓ₁′-data | ℓ₂′-data | f₁ , f₁-eq | f₂ , f₂-eq =
  (λ {s} {s′} → refl) ,
  (λ {v} {v′} → refl) ,
  (λ {s} → refl) ,
  lemma
  where lemma : {s : Σ S (λ x → S)} {v : Σ T (λ x → T)} →
                  Σ (R̂ (f₂ (f₁ (proj₂ s))) (proj₁ v))
                  (λ x → f₂ (f₁ (proj₂ s)) ≡ proj₂ v) →
                  (put (proj₁ (ℓ₁-data (proj₂ s))) (proj₁ s)
                  (put (proj₁ (ℓ₂-data (get (proj₁ (ℓ₁-data (proj₂ s))) (proj₂ s))))
                  (get (proj₁ (ℓ₁-data (proj₂ s))) (proj₁ s)) (proj₁ v))
                  , proj₂ s)
                  ≡
                (put (proj₁ (ℓ₁-data (proj₂ s))) (proj₁ s)
                (put (proj₁ (ℓ₂-data (f₁ (proj₂ s)))) (f₁ (proj₁ s)) (proj₁ v))
                  , proj₂ s)
        lemma {s , s′} (_ , _) rewrite f₁-eq s′ s′ | f₁-eq s′ s = refl


bxmap-depl-cong : ∀ {S V : Set} →
               {P̃ : S → S → Set} →
               {Q̃ : V → V → Set} →
               (a₀ : S) →
               (l₁-data : Σ (Lens (S × S) (V × V))
                           λ l → l hasConditions (CommonConditions.map-dep-cond {S} P̃)
                                   and            CommonConditions.map-dep-cond {V} Q̃) →
               (f₁-data : Σ (S → V) λ f →  (∀ {a a′} → get (proj₁ l₁-data) (a , a′) ≡ (f a , f a′))) →
               (l₂-data : Σ (Lens (S × S) (V × V))
                           λ l → l hasConditions (CommonConditions.map-dep-cond {S} P̃)
                                   and            CommonConditions.map-dep-cond {V} Q̃) →
               (f₂-data : Σ (S → V) λ f →  (∀ {a a′} → get (proj₁ l₂-data) (a , a′) ≡ (f a , f a′))) →
               (f₁≡f₂ : ∀ s → proj₁ f₁-data s ≡ proj₁ f₂-data s) →
               (l₁≈l₂ : proj₁ l₁-data ≈ proj₁ l₂-data) →
               bxmap-depl a₀ l₁-data f₁-data ≈ bxmap-depl a₀ l₂-data f₂-data
bxmap-depl-cong {S} {V} {P̃} {Q̃} a₀ (l₁ , l₁-conds) (f₁ , f₁-eq) (l₂ , l₂-conds) (f₂ , f₂-eq) f₁≡f₂
             (_ , _ , l-get-eq , l-put-eq)
  = (λ {s} {s′} → refl)
  , (λ {v} {v′} → Q-eq v v′)
  , (λ {s} → get-eq a₀ s)
  , λ {s} {v} → put-eq s v
  where
    Q-eq : (v v′ : List V) →
      (ConsecutivePairs Q̃ (f₁ a₀) v′
       × length v ≡ length v′)
      ≡
      (ConsecutivePairs Q̃ (f₂ a₀) v′
       × length v ≡ length v′)
    Q-eq v v′ rewrite f₁≡f₂ a₀ = refl
    get-eq : ∀ (a₀ : S) (s : List S) →
             Map-Helper.g-aux l₁ a₀ s ≡ Map-Helper.g-aux l₂ a₀ s
    get-eq a₀ [] = refl
    get-eq a₀ (x ∷ xs) rewrite l-get-eq {(x , a₀)} | get-eq x xs = refl
    put-eq′ : ∀ a₀ b₀ as bs → f₁ a₀ ≡ b₀ → ConsecutivePairs Q̃ b₀ bs × length (Map-Helper.g-aux l₁ a₀ as) ≡ length bs →
             Map-Helper.p-aux l₁ a₀ b₀ as bs ≡ Map-Helper.p-aux l₂ a₀ b₀ as bs
    put-eq′ a₀ b₀ [] [] eq₁ (cp-Q , eq-len) = refl
    put-eq′ a₀ .(f₁ a₀) (a ∷ as) (b ∷ bs) refl ((Q̃b₀b ∷ cp-Q̃) , eq-len)
      with l-put-eq {a , a₀} {b , f₁ a₀} | put-get-law-from-lens-data (l₁ , l₁-conds) {a , a₀} {b , f₁ a₀}
    ... | l-put-eq-pre | pg-eq-pre  with Q l₁ (get l₁ (a , a₀)) (b , f₁ a₀) |  cong-app (cong-app (proj₂ l₁-conds) (get l₁ (a , a₀))) (b , f₁ a₀)
    ... | .((Q̃ (proj₂ (get l₁ (a , a₀))) b) × proj₂ (get l₁ (a , a₀)) ≡ f₁ a₀) | refl with proj₂ (get l₁ (a , a₀)) | cong proj₂ (f₁-eq {a} {a₀})
    ... | .(f₁ a₀) | refl 
      = cong₂ _∷_
               (cong proj₁ (l-put-eq-pre (Q̃b₀b , refl)))
               (begin
                  Map-Helper.p-aux l₁ (proj₁ (put l₁ (a , a₀) (b , f₁ a₀))) b as bs
                ≡⟨ put-eq′ (proj₁ (put l₁ (a , a₀) (b , f₁ a₀))) b as bs
                           (cong proj₁
                                 (begin
                                    f₁ (proj₁ (put l₁ (a , a₀) (b , f₁ a₀))) , f₁ (proj₂ (put l₁ (a , a₀) (b , f₁ a₀)))
                                  ≡⟨ sym f₁-eq ⟩
                                    get l₁ (put l₁ (a , a₀) (b , f₁ a₀))
                                  ≡⟨ pg-eq-pre (Q̃b₀b , refl) ⟩
                                    b , f₁ a₀
                                  ∎))
                           (cp-Q̃ , (begin
                                      length (Map-Helper.g-aux l₁ (proj₁ (put l₁ (a , a₀) (b , f₁ a₀))) as)
                                    ≡⟨ Map-Helper.g-aux-length l₁ {proj₁ (put l₁ (a , a₀) (b , f₁ a₀))} {as} ⟩
                                       length as
                                    ≡⟨ sym (Map-Helper.g-aux-length l₁ {a} {as}) ⟩
                                       length (Map-Helper.g-aux l₁ a as)
                                    ≡⟨ suc-injective eq-len ⟩
                                       length bs
                                    ∎)) ⟩
                  Map-Helper.p-aux l₂ (proj₁ (put l₁ (a , a₀) (b , f₁ a₀))) b as bs
                ≡⟨ cong (λ a → Map-Helper.p-aux l₂ a b as bs) (cong proj₁ (l-put-eq-pre (Q̃b₀b , refl))) ⟩
                  Map-Helper.p-aux l₂ (proj₁ (put l₂ (a , a₀) (b , f₁ a₀))) b as bs
                ∎)
    put-eq : ∀ as bs → ConsecutivePairs Q̃ (f₁ a₀) bs × length (Map-Helper.g-aux l₁ a₀ as) ≡ length bs →
             Map-Helper.p-aux l₁ a₀ (f₁ a₀) as bs ≡ Map-Helper.p-aux l₂ a₀ (f₂ a₀) as bs
    put-eq as bs q rewrite put-eq′ a₀ (f₁ a₀) as bs refl q | f₁≡f₂ a₀ = refl
         


bxmap-depl-fusion
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
bxmap-depl-fusion {S} {V} {T} a₀ {P̃} {Q̃} {R̃} (l₁ , l₁-conds) (f₁ , f₁-eq) (l₂ , l₂-conds) (f₂ , f₂-eq)
  = (λ {as} {as′} → refl)
  , (λ {cs} {cs′} → refl)
  , (λ { {as} → get-fusion a₀ as } )
  , λ { {as} {cs} (cp-R̃ , eq-length) → put-fusion a₀ as cs cp-R̃ }
  where
    bxmap₁ = bxmap-depl a₀ (l₁ , l₁-conds) (f₁ , f₁-eq)
    bxmap₂ = bxmap-depl (f₁ a₀) (l₂ , l₂-conds) (f₂ , f₂-eq)
    l₃-data : Σ (Lens (S × S) (T × T)) λ l → l hasConditions (λ { (_ , a) (a′ , a′′) → P̃ a a′ × a ≡ a′′})
                                               and            λ { (_ , b) (b′ , b′′) → R̃ b b′ × b ≡ b′′}
    l₃-data
      = ((l₁ ； l₂ [ (λ {v} {v'} p
                       → transport′
                           (cong (λ pred → pred v v')
                                 (sym (trans (proj₂ l₁-conds) (sym (proj₁ l₂-conds))))) p)
                  , (λ {v} {v'} p
                       → transport′
                           (cong (λ pred → pred v v')
                                 (trans (proj₂ l₁-conds) (sym (proj₁ l₂-conds)))) p) ]))
        , (proj₁ l₁-conds) , proj₂ l₂-conds
    l₃ = proj₁ l₃-data
    l₃-conds = proj₂ l₃-data
    f₃-data : Σ (S → T) λ f₃ → ∀ {a a′} → get l₃ (a , a′) ≡ (f₃ a , f₃ a′)
    f₃-data = ((f₂ ∘ f₁) , λ {a} {a′} → begin
                                          get l₂ (get l₁ (a , a′))
                                        ≡⟨ cong (get l₂) f₁-eq ⟩
                                          get l₂ (f₁ a , f₁ a′)
                                        ≡⟨ f₂-eq ⟩
                                          (f₂ ∘ f₁) a , (f₂ ∘ f₁) a′
                                        ∎)

    f₃ = proj₁ f₃-data
    f₃-eq = proj₂ f₃-data
    bxmap₃ = bxmap-depl a₀ l₃-data f₃-data
    g₁-aux = Map-Helper.g-aux l₁
    g₂-aux = Map-Helper.g-aux l₂
    g₃-aux = Map-Helper.g-aux l₃
    get-fusion : ∀ a₀ as → (g₂-aux (f₁ a₀) ∘ g₁-aux a₀) as ≡ g₃-aux a₀ as
    get-fusion a₀ [] = refl
    get-fusion a₀ (a ∷ as) with proj₁ (get l₁ (a , a₀)) | cong proj₁ (f₁-eq {a} {a₀})
    ... | .(f₁ a) | refl = cong₂ _∷_
        (cong proj₁
          (begin
             get l₂ (f₁ a , f₁ a₀)
           ≡⟨ cong (get l₂) (sym f₁-eq) ⟩
             get l₂ (get l₁ (a , a₀))
           ∎))
        (get-fusion a as)
    p₁-aux = Map-Helper.p-aux l₁
    p₂-aux = Map-Helper.p-aux l₂
    p₃-aux = Map-Helper.p-aux l₃
    put-fusion : ∀ a₀ as cs →
                 ConsecutivePairs R̃ (f₂ (f₁ a₀)) cs →
                 p₁-aux a₀ (f₁ a₀) as (p₂-aux (f₁ a₀) (f₂ (f₁ a₀)) (g₁-aux a₀ as) cs) ≡ p₃-aux a₀ (f₃ a₀) as cs
    put-fusion a₀ [] [] [] = refl
    put-fusion a₀ [] (x ∷ cs) _ = refl -- failed branch
    put-fusion a₀ (x ∷ as) [] _ = refl -- failed branch
    put-fusion a₀ (a ∷ as) (c ∷ cs) (R̃c₀c ∷ cp-R̃)
      with f₁ a₀ | f₂ (f₁ a₀) | cong proj₂ (f₁-eq {a} {a₀}) | cong proj₂ (f₃-eq {a} {a₀})
    ... | .(proj₂ (get l₁ (a , a₀))) | .(proj₂ (get l₃ (a , a₀))) | refl | refl with f₃ a₀ | cong proj₂ (f₃-eq {a} {a₀})
    ... | .(proj₂ (get l₃ (a , a₀))) | refl
      with proj₂ (put l₂ (get l₁ (a , a₀)) (c , proj₂ (get l₂ (get l₁ (a , a₀)))))
         | proj₂  (change-transformation-from-lens-data (l₂ , l₂-conds) (R̃c₀c , refl))
    ... | .(proj₂ (get l₁ (a , a₀))) | refl
      = cong₂ _∷_
        (cong (λ x → proj₁ (put l₁ (a , a₀) x))
              (cong₂ _,_ refl (proj₂  (change-transformation-from-lens-data (l₂ , l₂-conds) (R̃c₀c , refl)))))
        (begin
           p₁-aux
             (proj₁
               (put l₁ (a , a₀)
                 (proj₁
                   (put l₂ (get l₁ (a , a₀)) (c , proj₂ (get l₂ (get l₁ (a , a₀)))))
                 , proj₂ (get l₁ (a , a₀)))))
             (proj₁
               (put l₂ (get l₁ (a , a₀)) (c , proj₂ (get l₂ (get l₁ (a , a₀))))))
             as
             (p₂-aux
               (proj₁
                 (put l₂ (get l₁ (a , a₀)) (c , proj₂ (get l₂ (get l₁ (a , a₀))))))
               c
               (g₁-aux a as)
               cs)
         ≡⟨ cong₂ (λ x y → p₁-aux x y as
                     (p₂-aux
                       (proj₁
                         (put l₂ (get l₁ (a , a₀)) (c , proj₂ (get l₂ (get l₁ (a , a₀))))))
                         c
                         (g₁-aux a as)
                         cs))
                  (cong (λ x → proj₁
                                 (put l₁ (a , a₀)
                                    (proj₁
                                       (put l₂ (get l₁ (a , a₀)) (c , proj₂ (get l₂ (get l₁ (a , a₀)))))
                                       , x)))
                        (proj₂ (change-transformation-from-lens-data (l₂ , l₂-conds) (R̃c₀c , refl))))
                  (trans (sym (cong proj₁ (put-get-law-from-lens-data (l₁ , l₁-conds)
                              (change-transformation-from-lens-data (l₂ , l₂-conds) (R̃c₀c , refl)))))
                         (cong proj₁ f₁-eq)) ⟩
           p₁-aux
             (proj₁ (put l₃ (a , a₀) (c , proj₂ (get l₃ (a , a₀)))))
             (f₁ (proj₁ (put l₃ (a , a₀) (c , proj₂ (get l₃ (a , a₀))))))
             as
             (p₂-aux
               (proj₁
                 (put l₂ (get l₁ (a , a₀)) (c , proj₂ (get l₂ (get l₁ (a , a₀))))))
               c
               (g₁-aux a as)
               cs)
         ≡⟨ cong₂ (λ x y → p₁-aux
                           (proj₁ (put l₃ (a , a₀) (c , proj₂ (get l₃ (a , a₀)))))
                           (f₁ (proj₁ (put l₃ (a , a₀) (c , proj₂ (get l₃ (a , a₀)))))) as
                           (p₂-aux x y (g₁-aux a as) cs))
                  ((trans (sym (cong proj₁ (put-get-law-from-lens-data (l₁ , l₁-conds)
                               (change-transformation-from-lens-data (l₂ , l₂-conds) (R̃c₀c , refl)))))
                          (cong proj₁ f₁-eq)))
                  (trans (sym (cong proj₁ (put-get-law-from-lens-data l₃-data (R̃c₀c , refl)))) (cong proj₁ f₃-eq)) ⟩
           p₁-aux
           (proj₁ (put l₃ (a , a₀) (c , proj₂ (get l₃ (a , a₀)))))
           (f₁ (proj₁ (put l₃ (a , a₀) (c , proj₂ (get l₃ (a , a₀)))))) as
           (p₂-aux
             (f₁ (proj₁ (put l₃ (a , a₀) (c , proj₂ (get l₃ (a , a₀))))))
             (f₂ (f₁ (proj₁ (put l₃ (a , a₀) (c , proj₂ (get l₃ (a , a₀)))))))
             (g₁-aux a as)
             cs)
         ≡⟨ cong (λ x → p₁-aux
                        (proj₁ (put l₃ (a , a₀) (c , proj₂ (get l₃ (a , a₀)))))
                        (f₁ (proj₁ (put l₃ (a , a₀) (c , proj₂ (get l₃ (a , a₀)))))) as
                        (p₂-aux
                          (f₁ (proj₁ (put l₃ (a , a₀) (c , proj₂ (get l₃ (a , a₀))))))
                          (f₂ (f₁ (proj₁ (put l₃ (a , a₀) (c , proj₂ (get l₃ (a , a₀)))))))
                          x
                          cs)) (Map-Helper.g-aux-independent l₁ {f-data = (f₁ , f₁-eq)}) ⟩ 
           p₁-aux
           (proj₁ (put l₃ (a , a₀) (c , proj₂ (get l₃ (a , a₀)))))
           (f₁ (proj₁ (put l₃ (a , a₀) (c , proj₂ (get l₃ (a , a₀)))))) as
           (p₂-aux
             (f₁ (proj₁ (put l₃ (a , a₀) (c , proj₂ (get l₃ (a , a₀))))))
             (f₂ (f₁ (proj₁ (put l₃ (a , a₀) (c , proj₂ (get l₃ (a , a₀)))))))
             (g₁-aux (proj₁ (put l₃ (a , a₀) (c , proj₂ (get l₃ (a , a₀))))) as)
             cs)
         ≡⟨ (put-fusion (proj₁ (put l₃ (a , a₀) (c , proj₂ (get l₃ (a , a₀))))) as cs
                        (transport′ (cong (λ c → ConsecutivePairs R̃ c cs)
                                          ((trans (sym (cong proj₁ (put-get-law-from-lens-data l₃-data (R̃c₀c , refl))))
                                                  (cong proj₁ f₃-eq)))) cp-R̃)) ⟩
           p₃-aux (proj₁ (put l₃ (a , a₀) (c , proj₂ (get l₃ (a , a₀)))))
           (f₃ (proj₁ (put l₃ (a , a₀) (c , proj₂ (get l₃ (a , a₀)))))) as cs
         ≡⟨ cong₂ (λ x y → p₃-aux x y as cs)
                  refl
                  (sym (trans (sym (cong proj₁ (put-get-law-from-lens-data l₃-data (R̃c₀c , refl)))) (cong proj₁ f₃-eq))) ⟩
           p₃-aux (proj₁ (put l₃ (a , a₀) (c , proj₂ (get l₃ (a , a₀)))))
            c as cs
         ∎)






---------------------------------------------------------
--| 3 useful instances of  bxmap-depl                 --|
---------------------------------------------------------

bxtails-dep-init : ∀ {A : Set} →
                 Lens (List A × List A)
                      ((∃[ xss ] (∃[ xs ] (tails {A} xs ≡ xss)))
                         × (∃[ xss ] (∃[ xs ] (tails {A} xs ≡ xss))))
bxtails-dep-init {A}
  = record
      { get = g
      ; put = p
      ; P = CommonConditions.map-dep-cond CommonConditions.is-init
      ; Q = CommonConditions.map-dep-cond CommonConditions.is-mapinit∘init
      ; backward-validity = λ {a} {b} → prop₁ a b
      ; forward-validity = λ {a} → prop₂ a a
      ; conditioned-get-put = λ {a} → cgp a
      ; conditioned-put-get = λ {a} {b} → cpg a b
      }
  where
    g : List A × List A → (∃[ xss ] (∃[ xs ] (tails {A} xs ≡ xss)))
                         × (∃[ xss ] (∃[ xs ] (tails {A} xs ≡ xss)))
    g (as , as′) = (tails as , as , refl) , (tails as′ , as′ , refl)
    p-aux : List A → List (List A) → (List A × List A)
    p-aux as′ []  = [] , as′
    p-aux as′ (as ∷ _) = as , as′
    p : List A × List A → (∃[ xss ] (∃[ xs ] (tails {A} xs ≡ xss)))
                         × (∃[ xss ] (∃[ xs ] (tails {A} xs ≡ xss))) →
        List A × List A
    p (_ , as′) ((xss , _ , _) , _) = p-aux as′ xss
    -- p (_ , as′) (([] , xs , eq) , _) = [] , as′
    -- p (_ , as′) ((xs′ ∷ xss , xs , eq) , _) = xs′ , as′
    prop₁ : (a : List A × List A)
            (b
              : ∃-syntax (λ xss → ∃-syntax (λ xs → tails xs ≡ xss)) ×
                ∃-syntax (λ xss → ∃-syntax (λ xs → tails xs ≡ xss))) →
            CommonConditions.map-dep-cond CommonConditions.is-mapinit∘init
            (g a) b →
            CommonConditions.map-dep-cond CommonConditions.is-init a (p a b)
    prop₁ (as , []) ((.(as′′ ∷ []) , a ∷ as₁ , eq₁) , .[] , .[] , .refl) (([] , as′′ , refl , []) , refl) with tails-cons a as₁
    prop₁ (as , []) ((.([] ++ (a ∷ []) ∷ []) , a ∷ [] , refl) , .[] , .[] , .refl) (([] , .(a ∷ []) , refl , []) , refl) | refl = (a , refl) , refl
    prop₁ (as , []) ((.([] ++ as′′ ∷ []) , a ∷ x ∷ as₁ , eq₁) , .[] , .[] , .refl) (([] , as′′ , refl , []) , refl) | eq with tails as₁
    prop₁ (as , []) ((.([] ++ as′′ ∷ []) , a ∷ x ∷ .[] , ()) , .[] , .[] , .refl) (([] , as′′ , refl , []) , refl) | refl | []
    prop₁ (as , []) ((.([] ++ as′′ ∷ []) , a ∷ x ∷ as₁ , ()) , .[] , .[] , .refl) (([] , as′′ , refl , []) , refl) | refl | .as₁ ∷ xss
    prop₁ (as , a′ ∷ as′) ((.(ass′′ ++ as′′ ∷ []) , as₁ , eq₁) , .(scanr _∷_ [] (a′ ∷ as′)) , .(a′ ∷ as′) , .refl)
          ((ass′′ , as′′ , refl , ptwise-is-init) , refl) with tails-cons a′ as′
    prop₁ (as , a′ ∷ as′) ((.([] ++ as′′ ∷ []) , as₁ , eq₁) , .(scanr _∷_ [] (a′ ∷ as′)) , .(a′ ∷ as′) , .refl)
          (([] , as′′ , refl , ptwise-is-init) , refl) | eq with tails as′
    prop₁ (as , a′ ∷ as′) ((.([] ++ as′′ ∷ []) , as₁ , eq₁) , .(scanr _∷_ [] (a′ ∷ as′)) , .(a′ ∷ as′) , .refl)
          (([] , as′′ , refl , ()) , refl) | eq | []
    prop₁ (as , a′ ∷ as′) ((.([] ++ as′′ ∷ []) , as₁ , eq₁) , .(scanr _∷_ [] (a′ ∷ as′)) , .(a′ ∷ as′) , .refl)
          (([] , as′′ , refl , ()) , refl) | eq | res ∷ res₁ 
    prop₁ (as , a′ ∷ as′) ((.((ass′′ ∷ ass′′₁) ++ as′′ ∷ []) , as₁ , eq₁) , .(scanr _∷_ [] (a′ ∷ as′)) , .(a′ ∷ as′) , .refl)
          ((ass′′ ∷ ass′′₁ , as′′ , refl , ptwise-is-init) , refl) | eq with tails as′
    prop₁ (as , a′ ∷ .[]) ((.(((a′ ∷ a′′ ∷ []) ∷ []) ++ as′′ ∷ []) , as₁ , eq₁) , .(scanr _∷_ [] (a′ ∷ [])) , .(a′ ∷ []) , .refl)
          ((.(a′ ∷ a′′ ∷ []) ∷ .[] , as′′ , refl , ((a′′ , refl) ∷ [])) , refl) | refl | [] = (a′′ , refl) , refl
    prop₁ (as , a′ ∷ .as′′′) ((.((as′′₁ ∷ ass′′) ++ as′′ ∷ []) , as₁ , eq₁) , .(scanr _∷_ [] (a′ ∷ as′′′)) , .(a′ ∷ as′′′) , .refl)
          ((as′′₁ ∷ ass′′ , as′′ , refl , ((a′′ , eq₂) ∷ ptwise-is-init)) , refl) | refl | as′′′ ∷ ass = (a′′ , eq₂) , refl
    prop₂ : (a a′ : List A × List A) →
            CommonConditions.map-dep-cond CommonConditions.is-init a a′ →
            CommonConditions.map-dep-cond CommonConditions.is-mapinit∘init
            (g a) (g a′)
    prop₂ (as₁ , as₂) (.(as₂ ++ a ∷ []) , .as₂) ((a , refl) , refl)
      = ((map (λ xs → xs ++ a ∷ []) (tails as₂))
      , ((a ∷ []) , ((sym (tails-snoc as₂ a))
      , CommonConditionsProperties.mapsnoc⇒ptwise-is-init (tails as₂) a))) , refl
    cgp : (a : List A × List A) →
          CommonConditions.map-dep-cond CommonConditions.is-init a a →
          p a (g a) ≡ a
    cgp (.(a ∷ []) , []) ((a , refl) , refl) = refl
    cgp (.(a′ ∷ as′ ++ a ∷ []) , a′ ∷ as′) ((a , refl) , refl) with tails-cons a′ (as′ ++ a ∷ [])
    ... | eq rewrite eq = refl
    cpg₁ : (a : List A × List A)
          (b
            : ∃-syntax (λ xss → ∃-syntax (λ xs → tails xs ≡ xss)) ×
              ∃-syntax (λ xss → ∃-syntax (λ xs → tails xs ≡ xss))) →
           CommonConditions.map-dep-cond CommonConditions.is-mapinit∘init (g a) b →
          proj₁ (proj₁ (g (p a b))) ≡ proj₁ (proj₁ b)
    cpg₁ (as , .as₂) ((.[] , [] , refl) , .(scanr _∷_ [] as₂) , as₂ , refl) ((ass′′ , as′′ , eq , ptwise-is-init) , refl) = refl
    cpg₁ (as , .as₂) ((.(scanr _∷_ [] (a ∷ as₁)) , a ∷ as₁ , refl) , .(scanr _∷_ [] as₂) , as₂ , refl) ((ass′′ , as′′ , eq , ptwise-is-init) , refl)
      with tails-cons a as₁
    ... | eq₁ rewrite eq₁ = eq₁
    cpg₂ : (a : List A × List A)
          (b
            : ∃-syntax (λ xss → ∃-syntax (λ xs → tails xs ≡ xss)) ×
              ∃-syntax (λ xss → ∃-syntax (λ xs → tails xs ≡ xss))) →
           CommonConditions.map-dep-cond CommonConditions.is-mapinit∘init (g a) b →
          proj₁ (proj₂ (g (p a b))) ≡ proj₁ (proj₂ b)
    cpg₂ (as , .as₂) ((.[] , [] , refl) , .(scanr _∷_ [] as₂) , as₂ , refl) ((ass′′ , as′′ , eq , ptwise-is-init) , refl) = refl
    cpg₂ (as , .as₂) ((.(scanr _∷_ [] (a ∷ as₁)) , a ∷ as₁ , refl) , .(scanr _∷_ [] as₂) , as₂ , refl) ((ass′′ , as′′ , eq , ptwise-is-init) , refl)
      with tails-cons a as₁
    ... | eq₁ rewrite eq₁ = refl
    cpg : (a : List A × List A)
          (b
            : ∃-syntax (λ xss → ∃-syntax (λ xs → tails xs ≡ xss)) ×
              ∃-syntax (λ xss → ∃-syntax (λ xs → tails xs ≡ xss))) →
           CommonConditions.map-dep-cond CommonConditions.is-mapinit∘init (g a) b →
          g (p a b) ≡ b
    cpg a b q = cong₂ _,_ (tails-list-unique (proj₁ (g (p a b))) (proj₁ b) (cpg₁ a b q))
                          (tails-list-unique (proj₂ (g (p a b))) (proj₂ b) (cpg₂ a b q))
    

spec-bxmap-sum : Lens ((∃[ xss ] (∃[ xs ] (tails {ℤω} xs ≡ xss))) × (∃[ xss ] (∃[ xs ] (tails {ℤω} xs ≡ xss))))
                      (List ℤω × List ℤω)
spec-bxmap-sum = record
                   { get = g
                   ; put = p
                   ; P = CommonConditions.map-dep-cond CommonConditions.is-mapinit∘init
                   ; Q = CommonConditions.map-dep-cond CommonConditions.is-mapminus-rear
                   ; backward-validity = λ {a} {b} → prop₁ a b
                   ; forward-validity = λ {a} → prop₂ a a
                   ; conditioned-get-put = λ {a} → cgp a
                   ; conditioned-put-get = λ {a} {b} → cpg a b
                   }
  where
    g-aux : List (List ℤω) × List (List ℤω) → List ℤω × List ℤω
    g-aux (ass , ass′) = (map sum ass , map sum ass′)
    g : ((∃[ xss ] (∃[ xs ] (tails {ℤω} xs ≡ xss))) × (∃[ xss ] (∃[ xs ] (tails {ℤω} xs ≡ xss)))) → List ℤω × List ℤω
    g ((ass , _) , (ass′ , _)) = g-aux (ass , ass′)
    p-aux₁ : (as : List ℤω) → (as′ : List ℤω) → ∃[ xss ] (∃[ xs ] (tails {ℤω} xs ≡ xss))
    p-aux₁ as [] = ([] , [] , refl) -- failed branch
    p-aux₁ as (a′ ∷ as′) = (map (λ t → t ++ last a′ as′ ∷ []) (tails as) ++ (last a′ as′ ∷ []) ∷ []
                        , as ++ (last a′ as′) ∷ [] , tails-snoc as (last a′ as′))
    p-aux₂ : (as : List ℤω) → (as′ : List ℤω) → ∃[ xss ] (∃[ xs ] (tails {ℤω} xs ≡ xss))
    p-aux₂ as _ = tails as , as , refl
    p : ((∃[ xss ] (∃[ xs ] (tails {ℤω} xs ≡ xss))) × (∃[ xss ] (∃[ xs ] (tails {ℤω} xs ≡ xss)))) →
         List ℤω × List ℤω →
         ((∃[ xss ] (∃[ xs ] (tails {ℤω} xs ≡ xss))) × (∃[ xss ] (∃[ xs ] (tails {ℤω} xs ≡ xss))))
    p (_ , .(tails as) , as , refl) (as′ , _) = p-aux₁ as as′ , p-aux₂ as as′
    prop₁ : (a
              : ∃-syntax (λ xss → ∃-syntax (λ xs → tails xs ≡ xss)) ×
                ∃-syntax (λ xss → ∃-syntax (λ xs → tails xs ≡ xss)))
            (b : List ℤω × List ℤω) →
            CommonConditions.map-dep-cond CommonConditions.is-mapminus-rear (g a) b →
            CommonConditions.map-dep-cond CommonConditions.is-mapinit∘init a (p a b)
    prop₁ (_ , .[] , [] , refl) (.(b ∷ []) , .[]) ((b , refl) , refl) = ([] , ((b ∷ []) , (refl , []))) , refl
    prop₁ (_ , .(tails (a′ ∷ as′)) , a′ ∷ as′ , refl)
          (.(map (ℤω._+_ b) (map sum (tails (a′ ∷ as′))) ++ b ∷ []) , .(map sum (tails (a′ ∷ as′)))) ((b , refl) , refl)
            rewrite cong (map sum) (tails-cons a′ as′)
      = (map
            (λ t →
               t ++
               last (b ℤω.+ (a′ ℤω.+ sum as′))
               (map (ℤω._+_ b) (map sum (tails as′)) ++ b ∷ [])
               ∷ [])
            (tails (a′ ∷ as′))
        ,
        ((last (b ℤω.+ (a′ ℤω.+ sum as′))
            (map (ℤω._+_ b) (map sum (tails as′)) ++ b ∷ [])
          ∷ []) , (refl , CommonConditionsProperties.mapsnoc⇒ptwise-is-init
                            (tails (a′ ∷ as′)) (last (b ℤω.+ (a′ ℤω.+ sum as′))
                                                     (map (ℤω._+_ b) (map sum (tails as′)) ++ b ∷ []))))) , refl
    prop₂ : (a a′
              : ∃-syntax (λ xss → ∃-syntax (λ xs → tails xs ≡ xss)) ×
                ∃-syntax (λ xss → ∃-syntax (λ xs → tails xs ≡ xss))) →
            CommonConditions.map-dep-cond CommonConditions.is-mapinit∘init a a′ →
            CommonConditions.map-dep-cond CommonConditions.is-mapminus-rear (g a) (g a′)
    prop₂ ((.(scanr _∷_ [] as₁) , as₁ , refl) , .[] , .[] , refl)
          ((.(scanr _∷_ [] as₃) , as₃ , refl) , .[] , [] , refl)
          (([] , as , eq₁ , []) , refl) = ((sum as) , (cong (map sum) (sym eq₁))) , refl
    prop₂ ((.(scanr _∷_ [] as₁) , as₁ , refl) , .(scanr _∷_ [] (x ∷ as₄)) , .(x ∷ as₄) , refl)
          ((.(scanr _∷_ [] as₃) , as₃ , refl) , .(scanr _∷_ [] (x ∷ as₄)) , x ∷ as₄ , refl)
          (([] , as , eq₁ , ptwise-is-init) , refl)
            with Pointwise CommonConditions.is-init (tails (x ∷ as₄)) []
               | cong (λ x → Pointwise CommonConditions.is-init x []) (tails-cons x as₄)
    prop₂ ((.(tails as₁) , as₁ , refl) , .(tails (x ∷ as₄)) , .(x ∷ as₄) , refl)
          ((.(tails as₃) , as₃ , refl) , .(tails (x ∷ as₄)) , x ∷ as₄ , refl)
          (([] , as , eq₁ , ()) , refl)
            | .(Pointwise (λ as₂ as′ → Σ ℤω (λ a → as₂ ++ a ∷ [] ≡ as′)) ((x ∷ as₄) ∷ scanr _∷_ [] as₄) []) | refl
    prop₂ ((.(scanr _∷_ [] as₁) , as₁ , refl) , .(scanr _∷_ [] (x ∷ as₄)) , .(x ∷ as₄) , refl)
          ((.(scanr _∷_ [] as₃) , as₃ , refl) , .(scanr _∷_ [] (x ∷ as₄)) , x ∷ as₄ , refl)
          ((as′ ∷ ass , as , eq₁ , ptwise-is-init) , refl)
            with Pointwise CommonConditions.is-init (tails (x ∷ as₄)) (as′ ∷ ass)
               | cong (λ x → Pointwise CommonConditions.is-init x (as′ ∷ ass)) (tails-cons x as₄)
    prop₂ ((.(tails as₁) , as₁ , refl) , .(tails (x ∷ as₄)) , .(x ∷ as₄) , refl)
          ((.(tails as₃) , as₃ , refl) , .(tails (x ∷ as₄)) , x ∷ as₄ , refl)
          ((.(x ∷ as₄ ++ a ∷ []) ∷ ass , as , eq₁ , ((a , refl) ∷ ptwise-is-init)) , refl)
            | .(Pointwise (λ as₂ as′ → Σ ℤω (λ a₁ → as₂ ++ a₁ ∷ [] ≡ as′))
                          ((x ∷ as₄) ∷ scanr _∷_ [] as₄) ((x ∷ as₄ ++ a ∷ []) ∷ ass))
            | refl  = (a , (begin
                              map sum (tails as₃)
                            ≡⟨ cong (map sum ∘ tails) (sym (tails-unique (x ∷ as₄ ++ a ∷ []) (ass ++ as ∷ []) as₃ eq₁)) ⟩
                              map sum (tails (x ∷ as₄ ++ a ∷ []))
                            ≡⟨ cong (map sum) (tails-snoc (x ∷ as₄) a) ⟩
                              map sum (map (λ xs → xs ++ a ∷ []) (tails (x ∷ as₄)) ++ (a ∷ []) ∷ [])
                            ≡⟨ Data.List.Properties.map-++-commute sum (map (λ xs → xs ++ a ∷ []) (tails (x ∷ as₄))) ((a ∷ []) ∷ []) ⟩
                              map sum (map (λ xs → xs ++ a ∷ []) (tails (x ∷ as₄))) ++ (sum (a ∷ [])) ∷ []
                            ≡⟨ cong (λ k → map sum (map (λ xs → xs ++ a ∷ []) (tails (x ∷ as₄))) ++ k ∷ [])
                                    (+-identityʳ a) ⟩
                              map sum (map (λ xs → xs ++ a ∷ []) (tails (x ∷ as₄))) ++ a ∷ []
                            ≡⟨ cong (λ k → k ++ a ∷ []) (map-fusion (λ xs → xs ++ a ∷ []) sum) ⟩
                              map (λ xs → sum (xs ++ a ∷ [])) (tails (x ∷ as₄)) ++ a ∷ []
                            ≡⟨ cong (λ f → map f (tails (x ∷ as₄)) ++ a ∷ [])
                                    (funext
                                      (λ xs → trans
                                                (trans (sum-++-commute xs (a ∷ []))
                                                       (cong (λ k → sum xs ℤω.+ k)
                                                             (+-identityʳ a)))
                                                (+-comm (sum xs) a) )) ⟩
                              map (λ xs → (ℤω._+_ a) (sum xs)) (tails (x ∷ as₄)) ++ a ∷ []
                            ≡⟨ cong (λ k → k ++ a ∷ []) (sym (map-fusion sum (ℤω._+_ a))) ⟩
                               map (ℤω._+_ a) (map sum (tails (x ∷ as₄))) ++ a ∷ []
                            ∎)) , refl
    cgp : (a
              : ∃-syntax (λ xss → ∃-syntax (λ xs → tails xs ≡ xss)) ×
                ∃-syntax (λ xss → ∃-syntax (λ xs → tails xs ≡ xss))) →
           CommonConditions.map-dep-cond CommonConditions.is-mapinit∘init a a →
           p a (g a) ≡ a
    cgp ((.[] , [] , refl) , .(scanr _∷_ [] as′) , as′ , refl) ((ass , as′′ , eq₁ , ptw) , refl) = refl
    cgp ((.(scanr _∷_ [] (a ∷ as)) , a ∷ as , refl) , .(scanr _∷_ [] as′) , as′ , refl) ((ass , as′′ , eq₁ , ptw) , refl)
      with map sum (tails (a ∷ as)) | cong (map sum) (tails-cons a as)
    ... | .(sum (a ∷ as) ∷ map sum (tails as)) | refl
      with CommonConditionsProperties.ptwise-is-init-tail⇒is-init as′ (a ∷ as) ass (as′′ , eq₁) ptw
    ... | a′ , eq
      = cong₂ _,_
              (tails-list-unique
                (map
                  (λ z →
                    z ++
                      last (a ℤω.+ foldr ℤω._+_ +0 as)
                           (map (foldr ℤω._+_ +0) (scanr _∷_ [] as)) ∷ [])
                  (scanr _∷_ [] as′)
                    ++
                    (last (a ℤω.+ foldr ℤω._+_ +0 as)
                          (map (foldr ℤω._+_ +0) (scanr _∷_ [] as)) ∷ []) ∷ []
                  ,
                  as′ ++ last (a ℤω.+ foldr ℤω._+_ +0 as)
                              (map (foldr ℤω._+_ +0) (scanr _∷_ [] as)) ∷ []
                  ,
                  tails-snoc as′
                    (last (a ℤω.+ foldr ℤω._+_ +0 as)
                          (map (foldr ℤω._+_ +0) (scanr _∷_ [] as)))) (tails (a ∷ as) , a ∷ as , refl)
                    (begin
                       map
                         (λ z →
                           z ++  last (a ℤω.+ foldr ℤω._+_ +0 as)
                                      (map (foldr ℤω._+_ +0) (scanr _∷_ [] as)) ∷ [])
                         (scanr _∷_ [] as′) ++
                         (last (a ℤω.+ foldr ℤω._+_ (+0) as)
                               (map (foldr ℤω._+_ (+0)) (scanr _∷_ [] as)) ∷ []) ∷ []
                      ≡⟨ sym (tails-snoc as′
                                         (last (a ℤω.+ foldr ℤω._+_ (+0) as)
                                               (map (foldr ℤω._+_ (+0)) (scanr _∷_ [] as)))) ⟩
                         tails
                           (as′ ++ last (a ℤω.+ foldr ℤω._+_ (+0) as)
                                        (map (foldr ℤω._+_ (+0)) (scanr _∷_ [] as)) ∷ [])
                      ≡⟨ cong (λ a′ → tails (as′ ++ a′ ∷ []))
                              (begin
                                 last (sum (a ∷ as))
                                      (map sum (tails as))
                               ≡⟨ map-last {a = a ∷ as} {as = tails as} sum ⟩
                                 sum (last (a ∷ as) (tails as))
                               ≡⟨ cong sum
                                       (last-snoc (trans (trans (sym (tails-snoc as′ a′))
                                                                (cong tails eq))
                                                         (tails-cons a as))) ⟩
                                  sum (a′ ∷ [])
                               ≡⟨ +-identityʳ a′ ⟩
                                  a′
                               ∎) ⟩
                         tails (as′ ++ a′ ∷ [])
                      ≡⟨ cong tails eq ⟩
                         tails (a ∷ as)
                      ∎)) refl
    cpg : (a
             : ∃-syntax (λ xss → ∃-syntax (λ xs → tails xs ≡ xss)) ×
               ∃-syntax (λ xss → ∃-syntax (λ xs → tails xs ≡ xss)))
           (b : List ℤω × List ℤω) →
           CommonConditions.map-dep-cond CommonConditions.is-mapminus-rear (g a) b →
           g (p a b) ≡ b
    cpg ((.(scanr _∷_ [] as) , as , refl) , .(scanr _∷_ [] as′) , as′ , refl) ([] , .(map (foldr ℤω._+_ +0) (scanr _∷_ [] as′))) (b′ , refl) = refl
    cpg ((.(scanr _∷_ [] as) , as , refl) , .(scanr _∷_ [] as′) , as′ , refl) (b ∷ bs , .(map (foldr ℤω._+_ +0) (scanr _∷_ [] as′))) ((b′ , eq) , refl)
      rewrite last-snoc (sym eq) = cong₂ _,_
                      (begin
                         map sum
                             (map (λ z → z ++ b′ ∷ []) (tails as′) ++ (b′ ∷ []) ∷ [])
                       ≡⟨ Data.List.Properties.map-++-commute sum (map (λ z → z ++ b′ ∷ []) (tails as′)) ((b′ ∷ []) ∷ []) ⟩
                         map sum (map (λ z → z ++ b′ ∷ []) (tails as′)) ++ sum (b′ ∷ []) ∷ []
                       ≡⟨ cong (λ x → map sum (map (λ z → z ++ b′ ∷ []) (tails as′)) ++ x ∷ [])
                               (Data.IntegerOmega.Properties.+-identityʳ b′) ⟩
                         map sum (map (λ z → z ++ b′ ∷ []) (tails as′)) ++ b′ ∷ []
                       ≡⟨ cong (λ xs → xs ++ b′ ∷ []) (map-fusion (λ z → z ++ b′ ∷ []) sum) ⟩
                         map (λ xs → sum (xs ++ b′ ∷ [])) (tails as′) ++ b′ ∷ []
                       ≡⟨ cong (λ f → map f (tails as′) ++ b′ ∷ [])
                               (funext λ xs
                                 → begin
                                     sum (xs ++ b′ ∷ [])
                                   ≡⟨ sum-++-commute xs (b′ ∷ []) ⟩
                                     sum xs ℤω.+ sum (b′ ∷ [])
                                   ≡⟨ +-comm (sum xs) (sum (b′ ∷ [])) ⟩
                                     sum (b′ ∷ []) ℤω.+ sum xs
                                   ≡⟨ cong (λ b → b ℤω.+ sum xs) (+-identityʳ b′) ⟩
                                     b′ ℤω.+ sum xs
                                   ∎) ⟩
                          map (λ xs → b′ ℤω.+ sum xs) (tails as′) ++ b′ ∷ []
                       ≡⟨ cong (λ bs → bs ++ b′ ∷ []) (sym (map-fusion sum (ℤω._+_ b′))) ⟩
                          map (ℤω._+_ b′) (map sum (tails as′)) ++ b′ ∷ []
                       ≡⟨ sym eq ⟩
                          b ∷ bs
                       ∎) refl

bxmaximum-dep : Lens (List ℤω × List ℤω) (ℤω × ℤω)
bxmaximum-dep = record
                  { get = g
                  ; put = p
                  ; P = CommonConditions.map-dep-cond CommonConditions.is-mapminus-rear
                  ; Q = CommonConditions.map-dep-cond CommonConditions.true-cond
                  ; backward-validity = λ {a} {b} → prop₁ a b
                  ; forward-validity = λ {a} → prop₂ a a
                  ; conditioned-get-put = λ {a} → cgp a
                  ; conditioned-put-get = λ {a} {b} → cpg a b
                  }
  where
    g : List ℤω × List ℤω → ℤω × ℤω
    g (as , as′) = maximum as , maximum as′
    p : List ℤω × List ℤω → ℤω × ℤω → List ℤω × List ℤω
    p (_ , as) (x , _) = map (λ z → z ℤω.+ (x ℤω.- maximum (as ++ +0 ∷ []))) (as ++ +0 ∷ []) , as
    prop₁ : (a : List ℤω × List ℤω) (b : ℤω × ℤω) →
            CommonConditions.map-dep-cond (λ _ _ → ⊤) (g a) b →
            CommonConditions.map-dep-cond CommonConditions.is-mapminus-rear a (p a b)
    prop₁ (as , as′) (b , .(foldr ℤω._⊔_ -∞ as′)) (tt , refl)
      = ((b ℤω.- (maximum (as′ ++ +0 ∷ [])))
      , (begin
           map
             (λ z →
                z ℤω.+ (b ℤω.- maximum (as′ ++ +0 ∷ [])))
             (as′ ++ +0 ∷ [])
         ≡⟨ Data.List.Properties.map-++-commute (λ z → z ℤω.+ (b ℤω.- (maximum (as′ ++ (+0) ∷ [])))) as′ (+0 ∷ []) ⟩
           map (λ z → z ℤω.+ (b - maximum (as′ ++ +0 ∷ []))) as′ ++ +0 ℤω.+ (b - maximum (as′ ++ +0 ∷ [])) ∷ []
         ≡⟨ cong (λ x → map (λ z → z ℤω.+ (b - maximum (as′ ++ +0 ∷ []))) as′ ++ x ∷ [])
                 (Data.IntegerOmega.Properties.+-identityˡ (b - maximum (as′ ++ +0 ∷ []))) ⟩
           map (λ z → z ℤω.+ (b - maximum (as′ ++ +0 ∷ []))) as′ ++ b - maximum (as′ ++ +0 ∷ []) ∷ []
         ≡⟨ cong (λ f → map f as′ ++ b - maximum (as′ ++ +0 ∷ []) ∷ [])
                 (funext λ z → Data.IntegerOmega.Properties.+-comm z (b - maximum (as′ ++ +0 ∷ []))) ⟩
           map (ℤω._+_ (b ℤω.- maximum (as′ ++ +0 ∷ [])))
             as′
             ++ b ℤω.- maximum (as′ ++ +0 ∷ []) ∷ []
         ∎)) , refl
    prop₂ : (a a′ : List ℤω × List ℤω) →
             CommonConditions.map-dep-cond CommonConditions.is-mapminus-rear a a′ →
             CommonConditions.map-dep-cond (λ _ _ → ⊤) (g a) (g a′)
    prop₂ (as₁ , as₂) (.(map (ℤω._+_ b) as₂ ++ b ∷ []) , .as₂) ((b , refl) , refl) = tt , refl
    cgp : (a : List ℤω × List ℤω) →
          CommonConditions.map-dep-cond CommonConditions.is-mapminus-rear a a →
          p a (g a) ≡ a
    cgp (.(map (ℤω._+_ b) as′ ++ b ∷ []) , as′) ((b , refl) , refl) rewrite maximum-map-snoc-promotion′ {b} {as′}
      = cong₂ _,_
        (begin
           map (λ z → z ℤω.+ b) (as′ ++ +0 ∷ [])
         ≡⟨ Data.List.Properties.map-++-commute (λ z → z ℤω.+ b) as′ (+0 ∷ []) ⟩
           map (λ z → z ℤω.+ b) as′ ++ +0 ℤω.+ b ∷ []
         ≡⟨ cong₂ (λ f b → map f as′ ++ b ∷ [])
                  (funext λ z → Data.IntegerOmega.Properties.+-comm z b)
                  (Data.IntegerOmega.Properties.+-identityˡ b) ⟩
           map (ℤω._+_ b) as′ ++ b ∷ []
         ∎)  refl
    cpg : (a : List ℤω × List ℤω) (b : ℤω × ℤω) →
          CommonConditions.map-dep-cond (λ _ _ → ⊤) (g a) b → g (p a b) ≡ b
    cpg (as , as′) (b , .(maximum as′)) (tt , refl)
      = cong₂ _,_ (begin
                     maximum (map (λ z → z ℤω.+ (b ℤω.- maximum (as′ ++ +0 ∷ []))) (as′ ++ +0 ∷ []))
                   ≡⟨ cong maximum
                           (Data.List.Properties.map-++-commute
                             (λ z → z ℤω.+ (b ℤω.- maximum (as′ ++ +0 ∷ []))) as′ (+0 ∷ [])) ⟩
                     maximum (map (λ z → z ℤω.+ (b ℤω.- maximum (as′ ++ +0 ∷ []))) as′ ++ +0 ℤω.+ (b ℤω.- maximum (as′ ++ +0 ∷ [])) ∷ [])
                   ≡⟨ cong (λ x → maximum (map (λ z → z ℤω.+ (b ℤω.- maximum (as′ ++ +0 ∷ []))) as′ ++ x ∷ []))
                           (Data.IntegerOmega.Properties.+-identityˡ (b - maximum (as′ ++ +0 ∷ []))) ⟩
                     maximum (map (λ z → z ℤω.+ (b ℤω.- maximum (as′ ++ +0 ∷ []))) as′ ++ b ℤω.- maximum (as′ ++ +0 ∷ []) ∷ [])
                   ≡⟨ cong (λ f → maximum (map f as′ ++ b ℤω.- maximum (as′ ++ +0 ∷ []) ∷ []))
                           (funext λ z → Data.IntegerOmega.Properties.+-comm z (b - maximum (as′ ++ +0 ∷ []))) ⟩
                     maximum (map (ℤω._+_ (b ℤω.- maximum (as′ ++ +0 ∷ []))) as′ ++ b ℤω.- maximum (as′ ++ +0 ∷ []) ∷ [])
                   ≡⟨ maximum-map-snoc-promotion {b ℤω.- maximum (as′ ++ +0 ∷ [])} {as′} ⟩
                     b ℤω.- maximum (as′ ++ +0 ∷ []) ℤω.+ maximum (as′ ++ +0 ∷ [])
                   ≡⟨ Data.IntegerOmega.Properties.+-assoc b (- maximum (as′ ++ +0 ∷ [])) (maximum (as′ ++ +0 ∷ [])) ⟩
                     b ℤω.+ (- maximum (as′ ++ +0 ∷ []) ℤω.+ maximum (as′ ++ +0 ∷ []))
                   ≡⟨ cong (ℤω._+_ b) (Data.IntegerOmega.Properties.+-comm (- maximum (as′ ++ +0 ∷ [])) (maximum (as′ ++ +0 ∷ []))) ⟩
                     b ℤω.+ (maximum (as′ ++ +0 ∷ []) ℤω.+ - maximum (as′ ++ +0 ∷ []))
                   ≡⟨ cong (ℤω._+_ b) (i≡j∧j≢-∞⇒i-j≡0 (maximum (as′ ++ +0 ∷ [])) (maximum (as′ ++ +0 ∷ [])) refl (maximum≢-∞-lemma as′)) ⟩
                     b ℤω.+ +0
                   ≡⟨ Data.IntegerOmega.Properties.+-identityʳ b ⟩
                     b
                   ∎) refl












---------------------------------------------------------
--| combinator bxscanl                                --|
---------------------------------------------------------

module Scan-Helper {S V : Set} (l : Lens (Maybe (S × V) × V) (V × V)) where

  g-aux : V → List S → List V
  g-aux b₀ = scanl (λ b a → proj₁ (get l (just (a , b) , b))) b₀

  g-aux-length : ∀ {b₀} {as} →
                 length (g-aux b₀ as) ≡ length as
  g-aux-length {b₀} {[]} = refl
  g-aux-length {b₀} {a ∷ as} = cong suc (g-aux-length {as = as})

  p-aux : V → V → List S → List V → List S
  p-aux old-b₀ b₀ [] [] = []
  p-aux old-b₀ b₀ [] (x ∷ bs) = [] -- failed branch
  p-aux old-b₀ b₀ (x ∷ as) [] = [] -- failed branch
  p-aux old-b₀ b₀ (a ∷ as) (b ∷ bs) with proj₁ (put l (just (a , old-b₀) , b₀) (b , b₀))
  ... | just (a′ , _) = a′ ∷ p-aux (proj₁ (get l (just (a , old-b₀) , old-b₀))) b as bs
  ... | nothing = []


bxscanl : ∀ {S V : Set} →
          {Q̃ : V → V → Set} →
          (b₀ : V) →
          (l-data : Σ (Lens (Maybe (S × V) × V) (V × V))
                          λ l → l hasConditions (CommonConditions.scanl-cond {S} {V}) 
                                  and            λ { (_ , b) (b′ , b′′) → Q̃ b b′ × b ≡ b′′ }) →
          (f-data
            : Σ (Maybe (S × V) → V)
              λ f → (∀ {x} {y} → get (proj₁ l-data) (x , y) ≡ (f x , y))) →
          Lens (List S) (List V)
bxscanl {S} {V} {Q̃} b₀ (l , l-conds) (f , f-eq₁)
  = record
      { get = g
      ; put = p
      ; P = λ as as′ → length as ≡ length as′
      ; Q = view-cond-aux b₀
      ; backward-validity = λ {a} {b} → prop₁ b₀ b₀ a b
      ; forward-validity = λ {a} → prop₂ b₀ a a
      ; conditioned-get-put = λ {a} _ → cgp b₀ a
      ; conditioned-put-get = λ {a} {b} → cpg b₀ b₀ a b
      }
  where
    open Scan-Helper
    view-cond-aux : V →  List V → List V → Set
    view-cond-aux b₀ bs bs′ = ConsecutivePairs Q̃ b₀ bs′ × length bs ≡ length bs′
    g : List S → List V
    g = g-aux l b₀
    p : List S → List V → List S
    p = p-aux l b₀ b₀
    prop₁ : ∀ old-b₀ b₀ (a : List S) (b : List V) →
            view-cond-aux b₀ (g-aux l old-b₀ a) b → length a ≡ length (p-aux l old-b₀ b₀  a b)
    prop₁ old-b₀ b₀ [] [] (_ , _) = refl
    prop₁ old-b₀ b₀ (a ∷ as) (b ∷ bs) (Q̃xy ∷ cp-Q̃ , eq-length)
      with change-transformation-from-lens-data (l , l-conds) {just (a , old-b₀) , b₀} {b , b₀}
    ... | prop₁-eq-pre with proj₂ (get l (just (a , old-b₀) , b₀)) | cong proj₂ (f-eq₁ {just (a , old-b₀)} {b₀})
    ... | .b₀ | refl with prop₁-eq-pre (Q̃xy , refl)
    ... | prop₁-eq with put l (just (a , old-b₀) , b₀) (b , b₀)
    ... | just (a′ , _) , _
      = cong suc (prop₁ (proj₁ (get l (just (a , old-b₀) , old-b₀))) b as bs (cp-Q̃ , suc-injective eq-length))
    prop₂ : ∀ b₀ → (a a′ : List S) →
            length a ≡ length a′ →
            view-cond-aux b₀ (g-aux l b₀ a) (g-aux l b₀ a′)
    prop₂ b₀ [] [] eq-length = [] , refl
    prop₂ b₀ (a ∷ as) (a′ ∷ as′) eq-length
      with proj₁ (forward-validity-from-lens-data (l , l-conds) {just (a′ , b₀) , b₀} (refl , refl))
    ... | Q̃xy with prop₂ (proj₁ (get l (just (a′ , b₀) , b₀))) as as′ (suc-injective eq-length)
    ... | (cp-Q̃ , eq)  rewrite cong proj₂ (f-eq₁ {just (a′ , b₀)} {b₀}) = Q̃xy ∷ cp-Q̃ , cong suc (begin
                  length (g-aux l (proj₁ (get l (just (a , b₀) , b₀))) as)
                ≡⟨ g-aux-length l {proj₁ (get l (just (a , b₀) , b₀))} {as} ⟩
                  length as
                ≡⟨ sym (g-aux-length l {proj₁ (get l (just (a′ , b₀) , b₀))} {as}) ⟩
                  length (g-aux l (proj₁ (get l (just (a′ , b₀) , b₀))) as)
                ≡⟨ eq ⟩
                  length (g-aux l (proj₁ (get l (just (a′ , b₀) , b₀))) as′)
                ∎)
    cgp : ∀ b₀ → (a : List S)  → p-aux l b₀ b₀ a (g-aux l b₀ a) ≡ a
    cgp b₀ [] = refl
    cgp b₀ (a ∷ as)
      with proj₁ (get l (just (a , b₀) , b₀)) , b₀
         | cong (λ b → proj₁ (get l (just (a , b₀) , b₀)) , b) (sym (cong proj₂ (f-eq₁ {just (a , b₀)} {b₀})))
    ... | .(get l (just (a , b₀) , b₀)) | refl with get-put-law-from-lens-data (l , l-conds) {just (a , b₀) , b₀} (refl , refl)
    ... | gp-eq with put l (just (a , b₀) , b₀) (get l (just (a , b₀) , b₀)) | gp-eq
    ... | .(just (a , b₀) , b₀) | refl = cong₂ _∷_ refl (cgp (proj₁ (get l (just (a , b₀) , b₀))) as)
    cpg : ∀ old-b₀ b₀ (a : List S) (b : List V) →
          view-cond-aux b₀ (g-aux l b₀ a) b → g-aux l b₀ (p-aux l old-b₀ b₀ a b) ≡ b
    cpg old-b₀ b₀ [] [] (_ , _) = refl
    cpg old-b₀ b₀ (a ∷ as) (b ∷ bs) (Q̃xy ∷ cp-Q̃ , eq-length)
      with change-transformation-from-lens-data (l , l-conds) {just (a , old-b₀) , b₀} {b , b₀}
    ... | prop₁-eq-pre with put-get-law-from-lens-data (l , l-conds) {just (a , old-b₀) , b₀} {b , b₀}
    ... | pg-eq-pre with proj₂ (get l (just (a , old-b₀) , b₀)) | cong proj₂ (f-eq₁ {just (a , old-b₀)} {b₀})
    ... | .b₀ | refl with prop₁-eq-pre (Q̃xy , refl) | pg-eq-pre (Q̃xy , refl)
    ... | prop₁-eq | pg-eq with put l (just (a , old-b₀) , b₀) (b , b₀) | prop₁-eq
    ... | just (a′ , .b₀) , .b₀ | refl , refl with get l (just (a′ , b₀) , b₀) | pg-eq
    ... | .(b , b₀) | refl = cong₂ _∷_  refl (cpg (proj₁ (get l (just (a , old-b₀) , old-b₀))) b as bs (cp-Q̃
                       , (begin
                            length (g-aux l b as)
                          ≡⟨ g-aux-length l {b} {as} ⟩
                            length as
                          ≡⟨ sym (g-aux-length l {proj₁ (get l (just (a , b₀) , b₀))} {as}) ⟩
                            length (g-aux l (proj₁ (get l (just (a , b₀) , b₀))) as)
                          ≡⟨ suc-injective eq-length ⟩
                            length bs
                          ∎)))









---------------------------------------------------------
--| combinator bxfoldl-inits                          --|
--| bxinits                                           --|
---------------------------------------------------------


module FoldlInits-Helper {S V : Set} (l : Lens (Maybe (S × V) × V) (V × V)) where

  g′ : V → List S → V
  g′ b₀ [] = b₀
  g′ b₀ (a ∷ as) = g′ (proj₁ (get l (just (a , b₀) , b₀))) as

  g′-computation
    : ∀ {b₀} {as} {a} →
      g′ b₀ (as ++ a ∷ []) ≡ proj₁ (get l (just (a , g′ b₀ as) , g′ b₀ as))
  g′-computation {b₀} {[]} {a} = refl
  g′-computation {b₀} {a′ ∷ as} {a} = g′-computation {proj₁ (get l (just (a′ , b₀) , b₀))} {as} {a}
      

  g-aux : V → List S × List S → V × V
  g-aux b₀ (as , as′) = g′ b₀ as , g′ b₀ as′

  p-aux : V → List S × List S → V × V → List S × List S
  p-aux b₀ ([] , as′) (b , b′) with put l (nothing , b′) (b , b′)
  ... | just (a , _) , _ = as′ ++ (a ∷ []) , as′
  ... | nothing , _ = [] , []
  p-aux b₀ (a ∷ as , as′) (b , b′) with put l (just (last a as , g′ b₀ (init (a ∷ as))) , b′) (b , b′)
  ... | just (a′ , _) , _ = as′ ++ (a′ ∷ []) , as′
  ... | nothing , _ = [] , []



bfoldlᵢₙᵢₜ-component-source-condition : {S V : Set} → (b : V) → Maybe (S × V) →  (m : Maybe (S × V)) → Set
bfoldlᵢₙᵢₜ-component-source-condition b _ (just (_ , b′)) = b ≡ b′
bfoldlᵢₙᵢₜ-component-source-condition b _ nothing = ⊥

bfoldlᵢₙᵢₜ-component : ∀ {S V : Set} →
                      (Q̂ : V → V → Set) →
                      (ℓ-data : (b : V) → Σ (Lens (Maybe (S × V)) V) λ ℓ → ℓ hasConditions bfoldlᵢₙᵢₜ-component-source-condition b
                                                                             and λ _ → Q̂ b) →
                      (Σ (Maybe (S × V) → V) λ f → ∀ (b : V) → (m : Maybe (S × V)) → get (proj₁ (ℓ-data b)) m ≡ f m) →
                      Σ (Σ (Lens (Maybe (S × V) × V) (V × V)) λ ℓ → ℓ hasConditions CommonConditions.foldl-cond {S} {V}
                                                                      and CommonConditions.map-dep-cond Q̂)
                        λ ℓ-data → Σ (Maybe (S × V) → V) λ f → ∀ {x} {y} → get (proj₁ ℓ-data) (x , y) ≡ (f x , y)
bfoldlᵢₙᵢₜ-component {S} {V} Q̂ ℓ-data (f , f-eq) = (l , refl , refl) , f , refl
  where
    l : Lens (Maybe (S × V) × V) (V × V)
    get l (m , b) = f m , b
    put l (m , b) (b′ , b′′) = put (proj₁ (ℓ-data b)) m b′ , b
    P l = CommonConditions.foldl-cond
    Q l = CommonConditions.map-dep-cond Q̂
    backward-validity l {m , b} {b′ , .b} (view-cond₁ , refl) with proj₂ (ℓ-data b)
    ... | source-cond-eq , view-cond-eq with cong (λ pred → pred (get (proj₁ (ℓ-data b)) m) b′) (sym view-cond-eq)
    ... | view-cond-eq-applied  with backward-validity (proj₁ (ℓ-data b)) {m} {b′} (transport′ view-cond-eq-applied view-cond₁)
    ... | ℓ-backward-validity with transport′ (cong (λ pred → pred m (put (proj₁ (ℓ-data b)) m b′)) source-cond-eq) ℓ-backward-validity
    ... | source-cond-applied with put (proj₁ (ℓ-data b)) m b′
    ... | just (x , y) = refl , source-cond-applied
    ... | nothing = source-cond-applied
    forward-validity l {just (a , b) , .b} (refl , refl) with proj₂ (ℓ-data b)
    ... | source-cond-eq , view-cond-eq with cong (λ pred → pred (just (a , b)) (just (a , b))) source-cond-eq
    ... | source-cond-eq-applied with forward-validity (proj₁ (ℓ-data b)) {just (a , b)} (transport′ (sym source-cond-eq-applied) refl)
    ... | ℓ-forward-validity rewrite f-eq b (just (a , b)) = transport′ (cong (λ pred → pred (f (just (a , b))) (f (just (a , b)))) view-cond-eq) ℓ-forward-validity , refl
    conditioned-get-put l {just (a , b) , .b} (refl , refl) with conditioned-get-put (proj₁ (ℓ-data b)) {just (a , b)}
    ... | cgp with proj₂ (ℓ-data b)
    ... | source-cond-eq , _ with cong (λ pred → pred (just (a , b)) (just (a , b))) source-cond-eq
    ... | source-cond-eq-applied rewrite f-eq b (just (a , b)) = cong₂ _,_ (cgp (transport′ (sym source-cond-eq-applied) refl)) refl
    conditioned-put-get l {m , b} {b′ , .b} (view-cond₁ , refl) with proj₂ (ℓ-data b)
    ... | _ , view-cond-eq with cong (λ pred → pred (get (proj₁ (ℓ-data b)) m) b′) (sym view-cond-eq)
    ... | view-cond-eq-applied with transport′ view-cond-eq-applied view-cond₁
    ... | view-cond′ with conditioned-put-get (proj₁ (ℓ-data b)) {m} {b′}
    ... | cpg rewrite f-eq b (put (proj₁ (ℓ-data b)) m b′) = cong₂ _,_ (cpg view-cond′) refl


bxfoldl-inits : ∀ {S V : Set} →
                {Q̃ : V → V → Set} →
                (b₀ : V) →
                (l-data : Σ (Lens (Maybe (S × V) × V) (V × V))
                          λ l → l hasConditions (CommonConditions.foldl-cond {S} {V} ) 
                                  and            CommonConditions.map-dep-cond Q̃) →
                (f-data
                  : Σ (Maybe (S × V) → V)
                    λ f → (∀ {x} {y} → get (proj₁ l-data) (x , y) ≡ (f x , y))) →
                Lens (List S × List S) (V × V)
bxfoldl-inits {S} {V} {Q̃} b₀ (l , l-conds) (f , f-eq₁)
  = record
      { get = g
      ; put = p
      ; P = source-cond
      ; Q = view-cond 
      ; backward-validity = λ {x} {y} → prop₁ x y 
      ; forward-validity = λ {a} → prop₂ a a
      ; conditioned-get-put = λ {a} → cgp a
      ; conditioned-put-get = λ {a} {b} → cpg a b
      }
  where
    open FoldlInits-Helper
    f-eq₃ : ∀ {x} {y} → proj₂ (get l (x , y)) ≡ y
    f-eq₃ {x} {y} = cong proj₂ f-eq₁
    source-cond : List S × List S → List S × List S → Set
    source-cond = CommonConditions.map-dep-cond CommonConditions.is-init
    view-cond : V × V → V × V → Set
    view-cond = CommonConditions.map-dep-cond Q̃
    g : List S × List S → V × V
    g = g-aux l b₀
    p : List S × List S → V × V → List S × List S
    p = p-aux l b₀
    prop₁ : (a : List S × List S) (b : V × V) →
            view-cond (g-aux l b₀ a) b → source-cond a (p-aux l b₀ a b)
    prop₁ ([] , as′) (b , .(g′ l b₀ as′)) (Q̃b₀b , refl)
      with change-transformation-from-lens-data (l , l-conds) {nothing , g′ l b₀ as′} {b , g′ l b₀ as′}
    ... | prop₁-eq-pre
      with proj₂ (get l (nothing , g′ l b₀ as′)) | cong proj₂ (f-eq₁ {nothing} {g′ l b₀ as′})
    ... | .(g′ l b₀ as′) | refl with prop₁-eq-pre (Q̃b₀b , refl)
    ... | prop₁-eq with put l (nothing , g′ l b₀ as′) (b , g′ l b₀ as′)
    ... | just (a , _) , _ = (a , refl) , refl
    prop₁ (a ∷ as , as′) (b , .(g′ l b₀ as′)) (Q̃b₀b , refl)
      with change-transformation-from-lens-data (l , l-conds)
                                                {just (last a as , g′ l b₀ (init (a ∷ as))) , g′ l b₀ as′}
                                                {b , g′ l b₀ as′}
    ... | prop₁-eq-pre
      with proj₂ (get l (just (last a as , g′ l b₀ (init (a ∷ as))) , g′ l b₀ as′))
         | cong proj₂ (f-eq₁ {just (last a as , g′ l b₀ (init (a ∷ as)))} {g′ l b₀ as′})
    ... | .(g′ l b₀ as′) | refl with prop₁-eq-pre (Q̃b₀b , refl)
    ... | prop₁-eq with put l (just (last a as , g′ l b₀ (init (a ∷ as))) , g′ l b₀ as′) (b , g′ l b₀ as′)
    ... | just (a′ , _) , _ = (a′ , refl) , refl
    prop₂ : (a a′ : List S × List S) →
            source-cond a a′ → view-cond (g-aux l b₀ a) (g-aux l b₀ a′)
    prop₂ (_ , []) (.(a ∷ []) , .[]) ((a , refl) , refl)
      with proj₁ (forward-validity-from-lens-data (l , l-conds) {just (a , b₀) , b₀} (refl , refl))
    ... | Q̃xy rewrite cong proj₂ (f-eq₁ {just (a , b₀)} {b₀})  = Q̃xy , refl
    prop₂ (_ , a′ ∷ as) (.(a′ ∷ as ++ a ∷ []) , .(a′ ∷ as)) ((a , refl) , refl)
      with proj₁ (forward-validity-from-lens-data (l , l-conds)
                                                             {just (a , g′ l b₀ (a′ ∷ as)) , g′ l b₀ (a′ ∷ as)}  (refl , refl))
    ... | Q̃xy
      rewrite g′-computation l {b₀} {a′ ∷ as} {a} | cong proj₂ (f-eq₁ {just (a , g′ l b₀ (a′ ∷ as))} {g′ l b₀ (a′ ∷ as)}) = Q̃xy , refl 
    cgp : (a : List S × List S) →
          source-cond a a → p-aux l b₀ a (g-aux l b₀ a) ≡ a
    cgp (.(a ∷ []) , []) ((a , refl) , refl)
      with change-transformation-from-lens-data (l , l-conds)
                                                {just (a , b₀) , proj₂ (g-aux l b₀ (a ∷ [] , []))}
                                                {g-aux l b₀ (a ∷ [] , [])}
    ... | prop₁-eq-pre with forward-validity-from-lens-data (l , l-conds) {just (a , b₀) , b₀}  (refl , refl)
    ... | Q̃xy , refl with prop₁-eq-pre (Q̃xy , cong proj₂ f-eq₁)
    ... | prop₁-eq with get-put-law-from-lens-data (l , l-conds) {just (a , b₀) , b₀} (refl , refl)
    ... | gp-eq with begin
                       get l (just (a , b₀) , b₀)
                     ≡⟨ cong₂ _,_ refl (cong proj₂ (f-eq₁ {just (a , b₀)} {b₀})) ⟩
                       proj₁ (get l (just (a , b₀) , b₀)) , b₀
                     ∎
    ... | eq rewrite eq | gp-eq = refl
    cgp (.(a′ ∷ as′ ++ a ∷ []) , a′ ∷ as′) ((a , refl) , refl)
      with last a′ (as′ ++ a ∷ []) | last-computation {x = a′} {xs = as′} {x′ = a}
    ... | .a | refl
      with init (a′ ∷ as′ ++ a ∷ []) | init-snoc (a′ ∷ as′) a
    ... | .(a′ ∷ as′) | refl
      with proj₁ (forward-validity-from-lens-data (l , l-conds)
                                                             {just (a , g′ l b₀ (a′ ∷ as′)) ,  g′ l b₀ (a′ ∷ as′)} (refl , refl))
    ... | Q̃xy
      with  proj₁ (get l  (just (a , g′ l b₀ (a′ ∷ as′)) ,  g′ l b₀ (a′ ∷ as′)))
          | g′-computation l {b₀} {a′ ∷ as′} {a}
    ... | .(g′ l b₀ (a′ ∷ as′ ++ a ∷ [])) | refl
      with change-transformation-from-lens-data (l , l-conds)
                                                {just (a , g′ l b₀ (a′ ∷ as′)) , g′ l b₀ (a′ ∷ as′)}
                                                {g′ l b₀ (a′ ∷ as′ ++ a ∷ []) , g′ l b₀ (a′ ∷ as′)}
    ... | prop₁-eq-pre with prop₁-eq-pre (Q̃xy , cong proj₂ f-eq₁)
    ... | prop₁-eq with get-put-law-from-lens-data (l , l-conds) {just (a , g′ l b₀ (a′ ∷ as′)) , g′ l b₀ (a′ ∷ as′)} 
    ... | gp-eq-pre  with gp-eq-pre (refl , refl)
    ... | gp-eq
      with get l (just (a , g′ l (proj₁ (get l (just (a′ , b₀) , b₀))) as′) , g′ l (proj₁ (get l (just (a′ , b₀) , b₀))) as′)
         | cong₂ _,_ (sym (g′-computation l {b₀} {a′ ∷ as′} {a}))
                     (cong proj₂ (f-eq₁ {just (a , g′ l b₀ (a′ ∷ as′))} {g′ l b₀ (a′ ∷ as′)}))
    ... | .(g′ l (proj₁ (get l (just (a′ , b₀) , b₀))) (as′ ++ a ∷ []) , g′ l (proj₁ (get l (just (a′ , b₀) , b₀))) as′) | refl
      with put l  (just (a , g′ l b₀ (a′ ∷ as′)) , g′ l b₀ (a′ ∷ as′))
                  (g′ l b₀ (a′ ∷ as′ ++ a ∷ []) , g′ l b₀ (a′ ∷ as′))
    cgp (.((a′ ∷ as′) ++ a ∷ []) , a′ ∷ as′) ((a , refl) , refl)
      | .a | refl | .(a′ ∷ as′) | refl | Q̃xy | .(g′ l (proj₁ (get l (just (a′ , b₀) , b₀))) (as′ ++ a ∷ []))
      | refl | prop₁-eq-pre | prop₁-eq | gp-eq-pre | refl
      | .(g′ l (proj₁ (get l (just (a′ , b₀) , b₀))) (as′ ++ a ∷ []) , g′ l (proj₁ (get l (just (a′ , b₀) , b₀))) as′)
      | refl | just (.a , _) , _ = refl
    cpg : (a : List S × List S) (b : V × V) →
          view-cond (g-aux l b₀ a) b → g-aux l b₀ (p-aux l b₀ a b) ≡ b
    cpg ([] , as′) (b , .(g′ l b₀ as′)) (Q̃xy , refl)
      with change-transformation-from-lens-data (l , l-conds) {nothing , g′ l b₀ as′} {b , g′ l b₀ as′}
    ... | prop₁-eq-pre with put-get-law-from-lens-data (l , l-conds) {nothing , g′ l b₀ as′} {b , g′ l b₀ as′}
    ... | pg-eq-pre with proj₂ (get l (nothing , g′ l b₀ as′)) | cong proj₂ (f-eq₁ {nothing} {g′ l b₀ as′})
    ... | .(g′ l b₀ as′) | refl with prop₁-eq-pre (Q̃xy , refl)
    ... | prop₁-eq with pg-eq-pre (Q̃xy , refl)
    ... | pg-eq with put l (nothing , g′ l b₀ as′) (b , g′ l b₀ as′)
    ... | just (a , x) , y with x | y | prop₁-eq
    ... | .(g′ l b₀ as′) | .(g′ l b₀ as′) | refl , refl
      rewrite g′-computation l {b₀} {as′} {a} = cong₂ _,_ (cong proj₁ pg-eq) refl  
    cpg (a ∷ as , as′) (b , .(g′ l b₀ as′)) (Q̃xy , refl)
      with change-transformation-from-lens-data (l , l-conds)
                                                {just (last a as , g′ l b₀ (init (a ∷ as))) , g′ l b₀ as′}
                                                {b , g′ l b₀ as′}
    ... | prop₁-eq-pre
      with put-get-law-from-lens-data (l , l-conds) {just (last a as , g′ l b₀ (init (a ∷ as))) , g′ l b₀ as′} {b , g′ l b₀ as′}
    ... | pg-eq-pre
      with proj₂ (get l (just (last a as , g′ l b₀ (init (a ∷ as))) , g′ l b₀ as′))
         | cong proj₂ (f-eq₁ {just (last a as , g′ l b₀ (init (a ∷ as)))} {g′ l b₀ as′})
    ... | .(g′ l b₀ as′) | refl with pg-eq-pre (Q̃xy , refl)
    ... | pg-eq with prop₁-eq-pre (Q̃xy , refl)
    ... | prop₁-eq with put l (just (last a as , g′ l b₀ (init (a ∷ as))) , g′ l b₀ as′) (b , g′ l b₀ as′)
    ... | just (a′ , x) , y with x | y | prop₁-eq
    ... | .(g′ l b₀ as′) | .(g′ l b₀ as′) | refl , refl
      rewrite g′-computation l {b₀} {as′} {a′} = cong₂ _,_ (cong proj₁ pg-eq) refl


bfoldlᵢₙᵢₜ : ∀ {S V : Set} →
             (Q̂ : V → V → Set) →
             (b₀ : V) →
             (ℓ-data : (b : V) → Σ (Lens (Maybe (S × V)) V) λ ℓ → ℓ hasConditions bfoldlᵢₙᵢₜ-component-source-condition b
                                                                    and λ _ b′ → Q̂ b b′) →
             (Σ (Maybe (S × V) → V) λ f → ∀ (b : V) → (m : Maybe (S × V)) → get (proj₁ (ℓ-data b)) m ≡ f m) →
             (Σ ((as : List S) → Σ (Lens (List S) V) λ ℓ → ℓ hasConditions (λ _ as′ → CommonConditions.is-init as as′) and λ _ b′ → Q̂ (get ℓ as) b′) λ ℓ-data → (Σ (List S → V) λ f → ∀ (as as′ : List S) → get (proj₁ (ℓ-data as)) as′ ≡ f as′))
bfoldlᵢₙᵢₜ {S} {V} Q̂ b₀ ℓ-data f-cond = Data.Product.uncurry (bmapl-component-reverse {Q̂ = Q̂}) ((Data.Product.uncurry (bxfoldl-inits {S} {V} {Q̂} b₀) component , refl , refl) , FoldlInits-Helper.g′ {S} {V} (proj₁ (proj₁ component)) b₀ , refl )
  where component = bfoldlᵢₙᵢₜ-component Q̂ ℓ-data f-cond



bscanl : ∀ {S V : Set} →
         {Q̂ : V → V → Set} →
         (b₀ : V) →
         (ℓ-data : (b : V) → Σ (Lens (Maybe (S × V)) V) λ ℓ → ℓ hasConditions bfoldlᵢₙᵢₜ-component-source-condition b
                                                                    and λ _ b′ → Q̂ b b′) →
         (Σ (Maybe (S × V) → V) λ f → ∀ (b : V) → (m : Maybe (S × V)) → get (proj₁ (ℓ-data b)) m ≡ f m) →
         Lens (List S) (List V)
bscanl {S} {V} {Q̂} b₀ ℓ-data f-data = Data.Product.uncurry (bxscanl {S} {V} {Q̂} b₀) component
  where component = bfoldlᵢₙᵢₜ-component Q̂ ℓ-data f-data
  

bxinits : ∀ {A : Set} → Lens (List A) (List (List A))
bxinits {A}
  = record
      { get = g
      ; put = p
      ; P = λ as as′ → length as ≡ length as′
      ; Q = λ bs bs′ → ConsecutivePairs Q̃ [] bs′ × length bs ≡ length bs′
      ; backward-validity = λ {a} {b} → prop₁ a b
      ; forward-validity = λ {a} eq-length → prop₂₁ [] a , prop₂₂ a a eq-length
      ; conditioned-get-put = λ {a} _ → cgp a
      ; conditioned-put-get = λ {xs} {ys} q → cpg xs ys (proj₁ q)
      }
  where
    g : List A → List (List A)
    g = inits
    p : List A → List (List A) → List A
    p = λ { _ [] → [] ; _ (xs ∷ xss) → last xs xss }
    Q̃ : List A → List A → Set
    Q̃ = CommonConditions.is-init
    prop₂₁ : (as₀ : List A) (as : List A) → ConsecutivePairs Q̃ as₀ (scanl (λ x y → x ++ y ∷ []) as₀ as)
    prop₂₁ as₀ [] = []
    prop₂₁ as₀ (a ∷ as) = (a , refl) ∷ prop₂₁ (as₀ ++ a ∷ []) as
    prop₂₂ : (as : List A) (as′ : List A) → length as ≡ length as′ → length (inits as) ≡ length (inits as′)
    prop₂₂ as as′ eq = begin
                          length (inits as)
                        ≡⟨ sym (length-inits [] as) ⟩
                          length as
                        ≡⟨ eq ⟩
                          length as′
                        ≡⟨ length-inits [] as′ ⟩
                          length (inits as′)
                        ∎
    cgp-aux : (as₀ : List A) (as : List A) → last as₀ (scanl (λ x y → x ++ y ∷ []) as₀ as) ≡ as₀ ++ as
    cgp-aux as₀ [] = sym (Data.List.Properties.++-identityʳ as₀)
    cgp-aux as₀ (a ∷ as)
      = begin
           last (as₀ ++ a ∷ []) (scanl (λ x y → x ++ y ∷ []) (as₀ ++ a ∷ []) as)
         ≡⟨ cgp-aux (as₀ ++ a ∷ []) as ⟩
           (as₀ ++ a ∷ []) ++ as
         ≡⟨ Data.List.Properties.++-assoc as₀ (a ∷ []) as ⟩
           as₀ ++ a ∷ as
         ∎
    cgp : (as : List A) → p as (g as) ≡ as
    cgp [] = refl
    cgp (a ∷ as) = cgp-aux (a ∷ []) as
    map-∷-cp-Q : ∀ ys₀ yss → ConsecutivePairs Q̃ ys₀ yss →
                 ∀ y → ConsecutivePairs Q̃ (y ∷ ys₀) (map (λ ys → y ∷ ys) yss)
    map-∷-cp-Q ys₀ [] cp-Q y = []
    map-∷-cp-Q ys₀ (.(ys₀ ++ y₁ ∷ []) ∷ yss) ((y₁ , refl) ∷ cp-Q) y = (y₁ , refl) ∷ map-∷-cp-Q (ys₀ ++ y₁ ∷ []) yss cp-Q y
    cp-Q-decompose : ∀ ys₀ yss →
                     ConsecutivePairs Q̃ ys₀ yss →
                     ∃[ yss′ ] (yss ≡ map (λ ys → ys₀ ++ ys) yss′ × ConsecutivePairs Q̃ [] yss′)
    cp-Q-decompose ys₀ [] [] = [] , refl , []
    cp-Q-decompose ys₀ (.(ys₀ ++ y ∷ []) ∷ yss) ((y , refl) ∷ cp-Q) with cp-Q-decompose (ys₀ ++ y ∷ []) yss cp-Q
    ... | yss′ , eq , cp-Q′ = (y ∷ []) ∷ map (λ ys → y ∷ ys) yss′
                              , cong₂ _∷_ refl (begin
                                                  yss
                                                ≡⟨ eq ⟩
                                                  map (λ ys → (ys₀ ++ y ∷ []) ++ ys) yss′
                                                ≡⟨ cong (λ f → map f yss′)
                                                        (funext λ ys → Data.List.Properties.++-assoc ys₀ (y ∷ []) ys) ⟩ 
                                                  map (λ ys → (ys₀ ++ (y ∷ [] ++ ys))) yss′
                                                ≡⟨ sym (map-fusion (_∷_ y) (_++_ ys₀)) ⟩
                                                  map (_++_ ys₀) (map (_∷_ y) yss′)
                                                ∎) , (y , refl) ∷ map-∷-cp-Q [] yss′ cp-Q′ y
    cpg-aux : ∀ xs yss →
              ∀ n → n ≡ length yss → -- n is used for termination checking
              ConsecutivePairs Q̃ [] yss → g (p xs yss) ≡ yss
    cpg-aux xs [] 0 eq-length cp-Q = refl
    cpg-aux xs (.(y ∷ []) ∷ yss) (suc n) eq-length ((y , refl) ∷ cp-Q) with cp-Q-decompose (y ∷ []) yss cp-Q
    ... | yss′ , eq , cp-Q′ with cpg-aux xs yss′ n (begin
                                                      n
                                                    ≡⟨ suc-injective eq-length ⟩
                                                      length yss
                                                    ≡⟨ cong length eq ⟩
                                                      length (map (List._∷_ y) yss′)
                                                    ≡⟨ Data.List.Properties.length-map (_∷_ y) yss′ ⟩
                                                      length yss′
                                                    ∎) cp-Q′
    cpg-aux xs (.([] ++ y ∷ []) ∷ .[]) (suc n) eq-length ((y , refl) ∷ cp-Q) | [] , refl , cp-Q′ | rec-eq = refl
    cpg-aux xs (.([] ++ y ∷ []) ∷ .((y ∷ ys′) ∷ map (_∷_ y) yss′)) (suc n) eq-length ((y , refl) ∷ cp-Q)
      | ys′ ∷ yss′ , refl , cp-Q′ | rec-eq
      rewrite map-last  {a = ys′} {as = yss′} (λ ys → y List.∷ ys) | inits-acc {xs₀ = y ∷ []} {xs = (last ys′ yss′)}
      = cong₂ _∷_ refl (cong (map (List._∷_ y)) rec-eq)
    cpg : (xs : List A) (yss : List (List A)) →
          ConsecutivePairs Q̃ [] yss → g (p xs yss) ≡ yss
    cpg xs yss cp-Q = cpg-aux xs yss (length yss) refl cp-Q
    prop₁ : (a : List A) (b : List (List A)) →
            ConsecutivePairs Q̃ [] b × length (g a) ≡ length b →
            length a ≡ length (p a b)
    prop₁ xs yss (cp-Q , eq-len)
      = begin
           length xs
         ≡⟨ length-inits [] xs ⟩
           length (g xs)
         ≡⟨ eq-len ⟩
           length yss
         ≡⟨ sym (cong length (cpg xs yss cp-Q)) ⟩
           length (g (p xs yss))
         ≡⟨ sym (length-inits [] (p xs yss)) ⟩
           length (p xs yss)
         ∎











--------------------------------------------------------------------------------------
--| a useful instance of list functor `algebra` used by bxfoldl-inits and bxscanl  --|
--------------------------------------------------------------------------------------

⊕-listf : Maybe (ℤω × ℤω) → ℤω
⊕-listf nothing = -∞
⊕-listf (just (x , y)) = (x ℤω.+ y) ℤω.⊔ x


bx-⊕ :  Lens (Maybe (ℤω × ℤω) × ℤω) (ℤω × ℤω)
bx-⊕ = record
         { get = g
         ; put = p
         ; P = CommonConditions.scanl-cond
         ; Q = CommonConditions.map-dep-cond CommonConditions.true-cond
         ; backward-validity = λ {a} {b} → prop₁ a b
         ; forward-validity = λ {a} → prop₂ a a
         ; conditioned-get-put = λ {a} → cgp a
         ; conditioned-put-get = λ {a} {b} → cpg a b
         }
  where
    g : Maybe (ℤω × ℤω) × ℤω → ℤω × ℤω
    g (mp , t) = ⊕-listf mp , t
    -- g (nothing , t) = (+0 , t)
    -- g (just (x , y) , t) = (x ℤω.+ y) ℤω.⊔ x , t
    p : Maybe (ℤω × ℤω) × ℤω → ℤω × ℤω → Maybe (ℤω × ℤω) × ℤω
    p (_ , c) (t , _) = just (t - (c ℤω.⊔ +0) , c) , c
    prop₁ : (a : Maybe (ℤω × ℤω) × ℤω) (b : ℤω × ℤω) →
            CommonConditions.map-dep-cond (λ _ _ → ⊤) (g a) b →
            proj₂ a ≡ proj₂ (p a b) × proj₂ a ≡ proj₂ a
    prop₁ (mp , c) (t , .(proj₂ (g (mp , c)))) (tt , refl) = refl , refl
    prop₂ : (a a′ : Maybe (ℤω × ℤω) × ℤω) →
            CommonConditions.scanl-cond a a′ →
            CommonConditions.map-dep-cond (λ _ _ → ⊤) (g a) (g a′)
    prop₂ (just x , .(proj₂ x₁)) (just x₁ , .(proj₂ x₁)) (refl , refl) = tt , refl
    prop₂ (nothing , .(proj₂ x)) (just x , .(proj₂ x)) (refl , refl) = tt , refl
    cgp : (a : Maybe (ℤω × ℤω) × ℤω) →
          CommonConditions.scanl-cond a a → p a (g a) ≡ a
    cgp (just (x , y) , .y) (refl , refl)
      = cong₂ _,_ (cong just (cong₂ _,_ (begin
                                           ((x ℤω.+ y) ℤω.⊔ x) - (y ℤω.⊔ +0)
                                         ≡⟨ cong (λ z → ((x ℤω.+ y) ℤω.⊔ z) - (y ℤω.⊔ +0))
                                                 (sym (Data.IntegerOmega.Properties.+-identityʳ x)) ⟩
                                           ((x ℤω.+ y) ℤω.⊔ (x ℤω.+ +0)) - (y ℤω.⊔ +0)
                                         ≡⟨ cong (λ z → z - (y ℤω.⊔ +0)) (sym (+-distribˡ-⊔ x y +0)) ⟩
                                           x ℤω.+ (y ℤω.⊔ +0) - (y ℤω.⊔ +0)
                                         ≡⟨ Data.IntegerOmega.Properties.+-assoc x (y ℤω.⊔ +0) (- (y ℤω.⊔ +0)) ⟩
                                           x ℤω.+ ((y ℤω.⊔ +0) - (y ℤω.⊔ +0))
                                         ≡⟨ cong (ℤω._+_ x) (i≡j∧j≢-∞⇒i-j≡0 (y ℤω.⊔ +0) (y ℤω.⊔ +0) refl (i⊔fin≢-∞ y (ℤ.+ ℕ.zero))) ⟩
                                           x ℤω.+ +0
                                         ≡⟨ Data.IntegerOmega.Properties.+-identityʳ x ⟩
                                           x
                                         ∎) refl)) refl
    cpg : (a : Maybe (ℤω × ℤω) × ℤω) (b : ℤω × ℤω) →
          CommonConditions.map-dep-cond (λ _ _ → ⊤) (g a) b →
          (proj₁ b - (proj₂ a ℤω.⊔ +0) ℤω.+ proj₂ a ℤω.⊔
            (proj₁ b - (proj₂ a ℤω.⊔ +0))
          , proj₂ (p a b))
          ≡ b
    cpg (mp , c) (t , .c) (tt , refl) = cong₂ _,_ (begin
                                                     (t - (c ℤω.⊔ +0) ℤω.+ c) ℤω.⊔ (t - (c ℤω.⊔ +0))
                                                   ≡⟨ cong (λ z → (t - (c ℤω.⊔ +0) ℤω.+ c) ℤω.⊔ z)
                                                           (sym (+-identityʳ (t ℤω.+ - (c ℤω.⊔ +0)))) ⟩
                                                     (t - (c ℤω.⊔ +0) ℤω.+ c) ℤω.⊔ (t - (c ℤω.⊔ +0) ℤω.+ +0)
                                                   ≡⟨ sym (+-distribˡ-⊔ (t - (c ℤω.⊔ +0)) c +0) ⟩
                                                     t - (c ℤω.⊔ +0) ℤω.+ (c ℤω.⊔ +0)
                                                   ≡⟨ +-assoc t (- (c ℤω.⊔ +0)) (c ℤω.⊔ +0) ⟩
                                                     t ℤω.+ (- (c ℤω.⊔ +0) ℤω.+ (c ℤω.⊔ +0))
                                                   ≡⟨ cong (ℤω._+_ t) (+-comm (- (c ℤω.⊔ +0)) (c ℤω.⊔ +0)) ⟩
                                                     t ℤω.+ ((c ℤω.⊔ +0) - (c ℤω.⊔ +0))
                                                   ≡⟨ cong (ℤω._+_ t) (i≡j∧j≢-∞⇒i-j≡0 (c ℤω.⊔ +0) (c ℤω.⊔ +0) refl (i⊔fin≢-∞ c (ℤ.+ ℕ.zero))) ⟩
                                                     t ℤω.+ +0
                                                   ≡⟨ +-identityʳ t ⟩
                                                     t 
                                                   ∎) refl
                                                     










---------------------------------------------------------
--| horner's rule                                     --|
--| bxscanl lemma                                     --|
---------------------------------------------------------

uni-hornor-rule-lemma : ∀ xs →
        (maximum ∘ map sum ∘ tails) (reverse xs) ≡ FoldlInits-Helper.g′ bx-⊕ -∞ (reverse xs)
uni-hornor-rule-lemma [] = refl
uni-hornor-rule-lemma (x ∷ xs)
  rewrite reverse-cons≡snoc x xs
        | FoldlInits-Helper.g′-computation bx-⊕ {b₀ = -∞} {as = reverse xs}  {a = x}
        | tails-snoc (reverse xs) x
        | Data.List.Properties.map-++-commute sum (map (λ xs₁ → xs₁ ++ x ∷ []) (tails (reverse xs))) ((x ∷ []) ∷ [])
        | map-fusion {xs = tails (reverse xs)} (λ xs₁ → xs₁ ++ x ∷ []) sum
        = begin
            maximum (map (λ xs → sum (xs ++ x ∷ [])) (tails (reverse xs)) ++ x ℤω.+ +0 ∷ [])
          ≡⟨ cong (λ z → maximum (map (λ xs → sum (xs ++ x ∷ [])) (tails (reverse xs)) ++ z ∷ []))
                  (Data.IntegerOmega.Properties.+-identityʳ x) ⟩
            maximum (map (λ xs → sum (xs ++ x ∷ [])) (tails (reverse xs)) ++ x ∷ [])
          ≡⟨ cong (λ f → maximum (map f (tails (reverse xs)) ++ x ∷ []))
                  (funext λ xs → begin
                                   sum (xs ++ x ∷ [])
                                 ≡⟨ sum-++-commute xs (x ∷ []) ⟩
                                   sum xs ℤω.+ sum (x ∷ [])
                                 ≡⟨ cong (λ x → sum xs ℤω.+ x) (Data.IntegerOmega.Properties.+-identityʳ x) ⟩
                                   sum xs ℤω.+ x
                                 ≡⟨ Data.IntegerOmega.Properties.+-comm (sum xs) x ⟩
                                   x ℤω.+ sum xs
                                 ∎) ⟩
                      maximum (map (λ xs → x ℤω.+ sum xs) (tails (reverse xs)) ++ x ∷ [])
                    ≡⟨ cong (λ xs₁ → maximum (xs₁ ++ x ∷ []))
                            (sym (map-fusion {xs = tails (reverse xs)} sum (ℤω._+_ x))) ⟩
                      maximum (map (ℤω._+_ x) (map sum (tails (reverse xs))) ++ x ∷ [])
                    ≡⟨ maximum-map-snoc-promotion {x} {map sum (tails (reverse xs))} ⟩
                      x ℤω.+ maximum (map sum (tails (reverse xs)) ++ +0 ∷ [])
                    ≡⟨ cong (ℤω._+_ x) (begin
                                         maximum (map sum (tails (reverse xs)) ++ +0 ∷ [])
                                       ≡⟨ maximum-snoc {map sum (tails (reverse xs))} {+0} ⟩
                                         maximum (map sum (tails (reverse xs))) ℤω.⊔ +0
                                       ≡⟨ cong (λ z → z ℤω.⊔ +0) (uni-hornor-rule-lemma xs) ⟩
                                         FoldlInits-Helper.g′ bx-⊕ -∞ (reverse xs) ℤω.⊔ +0
                                       ∎) ⟩ 
                      x ℤω.+ (FoldlInits-Helper.g′ bx-⊕ -∞ (reverse xs) ℤω.⊔ +0)
                    ≡⟨ +-distribˡ-⊔ x (FoldlInits-Helper.g′ bx-⊕ -∞ (reverse xs)) +0 ⟩
                      x ℤω.+ FoldlInits-Helper.g′ bx-⊕ -∞ (reverse xs) ℤω.⊔ (x ℤω.+ +0)
                    ≡⟨ cong (λ z → x ℤω.+ FoldlInits-Helper.g′ bx-⊕ -∞ (reverse xs) ℤω.⊔ z)
                            (Data.IntegerOmega.Properties.+-identityʳ x) ⟩
                      x ℤω.+ FoldlInits-Helper.g′ bx-⊕ -∞ (reverse xs) ℤω.⊔ x
                    ∎

uni-hornor-rule : ∀ xs →
                  (maximum ∘ map sum ∘ tails) xs ≡ FoldlInits-Helper.g′ bx-⊕ -∞ xs
uni-hornor-rule xs with uni-hornor-rule-lemma (reverse xs)
... | eq rewrite Data.List.Properties.reverse-involutive xs = eq


hornor-rule : bxtails-dep-init ；
              spec-bxmap-sum [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
              bxmaximum-dep [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ]
              ≈
              bxfoldl-inits {Q̃ = CommonConditions.true-cond} -∞ (bx-⊕ , refl , refl) (⊕-listf , (λ {_} {_} → refl))
hornor-rule = (λ {s} {s′} → refl)
            , (λ {v} {v′} → refl)
            , (λ {s} → get-eq s)
            , λ {s} {v} → put-eq s v
  where
    l₁ = bxtails-dep-init ；
         spec-bxmap-sum [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ] ；
         bxmaximum-dep [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ]
    l₂ = bxfoldl-inits {Q̃ = CommonConditions.true-cond} -∞ (bx-⊕ , refl , refl) (⊕-listf , (λ {_} {_} → refl) )
    get-eq′ : ∀ xs →
              (maximum ∘ map sum ∘ tails) xs ≡ FoldlInits-Helper.g′ bx-⊕ -∞ xs
    get-eq′ = uni-hornor-rule
    get-eq : (s : List ℤω × List ℤω) →
             get l₁ s  ≡ FoldlInits-Helper.g-aux bx-⊕ -∞ s
    get-eq (as , as′) = cong₂ _,_ (get-eq′ as) (get-eq′ as′)
    put-eq : (s : List ℤω × List ℤω) (v : ℤω × ℤω) →
             CommonConditions.map-dep-cond (λ _ _ → ⊤) (get l₁ s) v →
             put l₁ s v ≡ FoldlInits-Helper.p-aux bx-⊕ -∞ s v
    put-eq ([] , []) (b , .(-∞)) (tt , refl)
      rewrite maximum-singleton +0 | Data.IntegerOmega.Properties.+-identityˡ (b ℤω.+ +0) = refl
    put-eq (a ∷ as , []) (b , .(-∞)) (tt , refl)
      rewrite maximum-singleton +0 | Data.IntegerOmega.Properties.+-identityˡ (b ℤω.+ +0) = refl
    put-eq ([] , a′ ∷ as′) (b , .(maximum (map (foldr ℤω._+_ +0) (scanr _∷_ [] (a′ ∷ as′))))) (tt , refl)
      rewrite tails-cons a′ as′
            | tails-cons a′ as′
            | map-last {a = a′ ℤω.+ sum as′} {as = map sum (tails as′) ++ +0 ∷ []}
                       (λ z →
                         z ℤω.+
                         (b ℤω.+
                           -
                           (a′ ℤω.+ sum as′ ℤω.⊔
                             maximum
                               (map sum (tails as′) ++ +0 ∷ []))))
            | last-computation {x = a′ ℤω.+ sum as′} {xs = map sum (tails as′)} {x′ = +0}
            | maximum-snoc {map sum (tails as′)} {+0}
            | Data.IntegerOmega.Properties.⊔-assoc (a′ ℤω.+ sum as′) (maximum (map sum (tails as′))) +0
            = cong₂ _,_
                    (cong (λ xs → a′ ∷ as′ ++ xs) (cong (λ xs → xs ∷ [])
                    (Data.IntegerOmega.Properties.+-identityˡ
                      (b ℤω.+
                        -
                        (a′ ℤω.+ sum as′ ℤω.⊔
                          (maximum
                            (map sum (tails as′))
                              ℤω.⊔ +0)))))) refl
    put-eq (a ∷ as , a′ ∷ as′) (b , .(maximum (map (foldr ℤω._+_ +0) (scanr _∷_ [] (a′ ∷ as′))))) (tt , refl)
      rewrite tails-cons a′ as′
            | tails-cons a′ as′
            | map-last {a = a′ ℤω.+ sum as′} {as = map sum (tails as′) ++ +0 ∷ []}
                       (λ z →
                         z ℤω.+
                         (b ℤω.+
                           -
                           (a′ ℤω.+ sum as′ ℤω.⊔
                             maximum
                             (map sum (tails as′) ++ +0 ∷ []))))
            | last-computation {x = a′ ℤω.+ sum as′} {xs = map sum (tails as′)} {x′ = +0}
            | maximum-snoc {map sum (tails as′)} {+0}
            | Data.IntegerOmega.Properties.⊔-assoc (a′ ℤω.+ sum as′) (maximum (map sum (tails as′))) +0
            = cong₂ _,_
                    (cong (λ xs → a′ ∷ as′ ++ xs)
                          (cong (λ xs → xs ∷ [])
                                (Data.IntegerOmega.Properties.+-identityˡ
                                  (b ℤω.+
                                    -
                                    (a′ ℤω.+ sum as′ ℤω.⊔
                                      (maximum
                                        (map sum (tails as′))
                                        ℤω.⊔ +0)))))) refl


bxscanl-lemma : ∀ {S V : Set} →
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
bxscanl-lemma {S} {V} {Q̃} b₀ (l , l-conds) (f , f-eq₁)
  = (λ {s} {s′} → refl)
  , (λ {v} {v′} → refl)
  , (λ {s} → get-fusion s)
  , λ { {s} {v′} (cp-Q , eq-len) → put-fusion s v′ (cp-Q , eq-len) }
  where
    l₁ = bxinits
    bxfold-inits-data : Σ (Lens (List S × List S) (V × V))
                (λ l →
                  l hasConditions
                  CommonConditions.map-dep-cond CommonConditions.is-init and
                  CommonConditions.map-dep-cond Q̃)
    bxfold-inits-data  = bxfoldl-inits b₀ (l , l-conds) (f , f-eq₁) , refl , refl
    l₂ = bxmap-depl {P̃ = CommonConditions.is-init} {Q̃ = Q̃}
                    []
                    bxfold-inits-data (FoldlInits-Helper.g′ l b₀ , λ {a} {a′} → refl)
    l₃ = bxscanl b₀ (l , l-conds) (f , f-eq₁)
    get-fusion-aux : ∀ b xs₀ xs →
                  b ≡ FoldlInits-Helper.g′ l b₀ xs₀ → 
                  Map-Helper.g-aux (proj₁ bxfold-inits-data)
                                   xs₀
                                   (scanl (λ x y → x ++ y ∷ []) xs₀ xs)
                  ≡
                  Scan-Helper.g-aux l b xs
    get-fusion-aux b xs₀ [] eq = refl
    get-fusion-aux b xs₀ (x ∷ xs) eq
      rewrite FoldlInits-Helper.g′-computation l {b₀} {xs₀} {x}
            | sym eq
            = cong₂ _∷_ refl (get-fusion-aux (proj₁ (get l (just (x , b) , b))) (xs₀ ++ x ∷ []) xs (begin
                            proj₁ (get l (just (x , b) , b))
                          ≡⟨ cong (λ b → proj₁ (get l (just (x , b) , b))) eq ⟩
                            proj₁ (get l (just (x , FoldlInits-Helper.g′ l b₀ xs₀) , FoldlInits-Helper.g′ l b₀ xs₀))
                          ≡⟨ sym (FoldlInits-Helper.g′-computation l {b₀} {xs₀} {x}) ⟩
                            FoldlInits-Helper.g′ l b₀ (xs₀ ++ x ∷ [])
                          ∎))
    get-fusion : ∀ xs →
                 get l₂ (get l₁ xs) ≡ get l₃ xs
    get-fusion xs = get-fusion-aux b₀ [] xs refl
    put-fusion-aux : ∀ b₀′ b₀′′ as₀ as₀′ as bs →
                      b₀′ ≡ FoldlInits-Helper.g′ l b₀ as₀ →
                      ConsecutivePairs Q̃ b₀′′ bs × length (get l₂ (get l₁ as)) ≡ length bs →
                      Map-Helper.p-aux (proj₁ bxfold-inits-data)
                        as₀′ b₀′′ (scanl (λ x y → x ++ y ∷ []) as₀ as) bs
                      ≡
                      scanl (λ x y → x ++ y ∷ [])
                        as₀′
                        (Scan-Helper.p-aux l b₀′ b₀′′ as bs)
    put-fusion-aux b₀′ b₀′′ as₀ as₀′ [] [] eq (cp-Q̃ , eq-len) = refl
    put-fusion-aux b₀′ b₀′′ [] as₀′ (a ∷ as) (b ∷ bs) refl ((Q̃xy ∷ cp-Q̃) , eq-len)
      with change-transformation-from-lens-data (l , l-conds) {just (a , b₀′) , b₀′′} {b , b₀′′}
    ... | prop₁-eq-pre₂ with proj₂ (get l (just (a , b₀′) , b₀′′)) | cong proj₂ (f-eq₁ {just (a , b₀′)} {b₀′′})
    ... | .b₀′′ | refl with prop₁-eq-pre₂ (Q̃xy , refl)
    ... | prop₁-eq₂ with put l (just (a , b₀′) , b₀′′) (b , b₀′′)
    ... | just (a′ , _) , _
      = cong₂ _∷_
              refl
              (put-fusion-aux (proj₁ (get l (just (a , b₀′) , b₀′))) b (a ∷ []) (as₀′ ++ a′ ∷ []) as bs refl
                (cp-Q̃ , (begin
                           length (get l₂ (get l₁ as))
                         ≡⟨ Map-Helper.g-aux-length (proj₁ bxfold-inits-data) {a₀ = []} {as = get l₁ as} ⟩
                           length (get l₁ as)
                         ≡⟨ sym (length-inits [] as) ⟩
                           length as
                         ≡⟨ length-inits (a ∷ []) as ⟩
                           length (scanl (λ x y → x ++ y ∷ []) (a ∷ []) as)
                         ≡⟨ sym (Map-Helper.g-aux-length (proj₁ bxfold-inits-data)
                                                         {a₀ = a ∷ []}
                                                         {scanl (λ x y → x ++ y ∷ []) (a ∷ []) as}) ⟩
                           length (Map-Helper.g-aux (proj₁ bxfold-inits-data) (a ∷ [])
                                                    (scanl (λ x y → x ++ y ∷ []) (a ∷ []) as))
                         ≡⟨ suc-injective eq-len ⟩
                           length bs
                         ∎)))
    put-fusion-aux .(FoldlInits-Helper.g′ l (proj₁ (get l (just (a₀ , b₀) , b₀))) as₀)
                   b₀′′ (a₀ ∷ as₀) as₀′ (a ∷ as) (b ∷ bs) refl ((Q̃xy ∷ cp-Q̃) , eq-len)
                   with last a₀ (as₀ ++ a ∷ [])
                      | last-computation {x = a₀} {xs = as₀} {x′ = a}
                      | init (a₀ ∷ as₀ ++ a ∷ [])
                      | init-snoc (a₀ ∷ as₀) a
    ... | .a | refl | .(a₀ ∷ as₀) | refl
      with change-transformation-from-lens-data (l , l-conds)
                                                {just (a , FoldlInits-Helper.g′ l (proj₁ (get l (just (a₀ , b₀) , b₀))) as₀) , b₀′′}
                                                {b , b₀′′}
    ... | prop₁-eq-pre₂
      with proj₂ (get l (just (a , FoldlInits-Helper.g′ l (proj₁ (get l (just (a₀ , b₀) , b₀))) as₀) , b₀′′))
         | cong proj₂ (f-eq₁ {just (a , FoldlInits-Helper.g′ l (proj₁ (get l (just (a₀ , b₀) , b₀))) as₀)} {b₀′′})
    ... | .b₀′′ | refl with prop₁-eq-pre₂ (Q̃xy , refl)
    ... | prop₁-eq₂
      with put l (just (a , FoldlInits-Helper.g′ l (proj₁ (get l (just (a₀ , b₀) , b₀))) as₀) , b₀′′) (b , b₀′′)
    ... | just (a′ , _) , _
      = cong₂ _∷_ refl
                  (put-fusion-aux (proj₁
                    (get l
                      (just
                        (a ,
                        FoldlInits-Helper.g′ l (proj₁ (get l (just (a₀ , b₀) , b₀))) as₀)
                      ,
                      FoldlInits-Helper.g′ l (proj₁ (get l (just (a₀ , b₀) , b₀))) as₀)))
                    b (a₀ ∷ as₀ ++ a ∷ []) (as₀′ ++ a′ ∷ [])
                    as bs
                    (sym (FoldlInits-Helper.g′-computation l {proj₁ (get l (just (a₀ , b₀) , b₀))} {as₀} {a}))
                    (cp-Q̃ , (begin
                               length (get l₂ (get l₁ as))
                             ≡⟨ Map-Helper.g-aux-length (proj₁ bxfold-inits-data) {a₀ = []} {as = get l₁ as} ⟩
                               length (get l₁ as)
                             ≡⟨ sym (length-inits [] as) ⟩
                               length as
                             ≡⟨ length-inits (a ∷ []) as ⟩
                               length (scanl (λ x y → x ++ y ∷ []) (a ∷ []) as)
                             ≡⟨ sym (Map-Helper.g-aux-length (proj₁ bxfold-inits-data)
                                                             {a₀ = a ∷ []} {scanl (λ x y → x ++ y ∷ []) (a ∷ []) as}) ⟩
                               length (Map-Helper.g-aux (proj₁ bxfold-inits-data) (a ∷ [])
                                                    (scanl (λ x y → x ++ y ∷ []) (a ∷ []) as))
                             ≡⟨ suc-injective eq-len ⟩
                               length bs
                             ∎)))
    put-fusion : ∀ xs ys →
                 ConsecutivePairs Q̃ b₀ ys × length (get l₂ (get l₁ xs)) ≡ length ys → 
                 put l₁ xs (put l₂ (get l₁ xs) ys) ≡ put l₃ xs ys
    put-fusion xs ys (cp-Q̃ , eq-len)
      = inits-injective
                  (put l₁ xs (put l₂ (get l₁ xs) ys)) (put l₃ xs ys)
                  (begin
                     get l₁ (put l₁ xs (put l₂ (get l₁ xs) ys))
                   ≡⟨ conditioned-put-get l₁ {xs} {put l₂ (get l₁ xs) ys}
                                             (backward-validity l₂ {get l₁ xs} {ys} (cp-Q̃ , eq-len)) ⟩
                     put l₂ (get l₁ xs) ys
                   ≡⟨ put-fusion-aux b₀ b₀ [] [] xs ys refl (cp-Q̃ , eq-len) ⟩
                     get l₁ (put l₃ xs ys)
                   ∎)













---------------------------------------------------------
--| bidirectional fold, map                           --|
--| bidirectional fold fusion, fold map fusion        --|
---------------------------------------------------------


{-# TERMINATING #-}
unfold′ : ∀ {A : Set} {B : Set} →
          (coalg : B → Maybe (A × B)) →
          B → List A
unfold′ coalg b with coalg b
... | just (a , b') = a ∷ unfold′ coalg b'
... | nothing       = []


bxfold-conditioned : ∀ {S : Set} {V : Set} →
                     (P : S → S → Set) →
                     (Q : V → V → Set) →
                     (bxalg-data : Σ (Lens (Maybe (S × V)) V)
                                   λ l → l hasConditions (CommonConditions.lift P Q)
                                           and           Q) →
                     Lens (List S) V
get (bxfold-conditioned _ _ (bxalg , _)) = foldr (λ { a b → get bxalg (just (a , b)) }) (get bxalg nothing)
put (bxfold-conditioned _ _ (bxalg , _)) [] y = unfold′ (put bxalg nothing) y
put (bxfold-conditioned _ _ (bxalg , _)) (x ∷ xs) y with put bxalg (just (x , foldr (λ { a b → get bxalg (just (a , b)) }) (get bxalg nothing) xs)) y
put (bxfold-conditioned P Q bxalg-data) (x ∷ xs) y | just (x′ , y′) = x′ ∷ put (bxfold-conditioned P Q bxalg-data) xs y′
put (bxfold-conditioned _ _ _) (x ∷ xs) y | nothing = []
P (bxfold-conditioned P Q _) = CommonConditions.licond P
Q (bxfold-conditioned _ Q _) = Q
backward-validity(bxfold-conditioned P Q (bxalg , refl , refl)) {[]} {y} qxy with backward-validity bxalg qxy
... | pxy with put bxalg nothing y
backward-validity(bxfold-conditioned P Q (bxalg , refl , refl)) {[]} {y} qxy | CommonConditions.nothing | .nothing = refl , []
backward-validity(bxfold-conditioned P Q (bxalg , refl , refl)) {x ∷ xs} {y} qxy with backward-validity bxalg qxy
... | pxy with put bxalg (just (x , foldr (λ a b → get bxalg (just (a , b))) (get bxalg nothing) xs)) y
backward-validity(bxfold-conditioned P Q (bxalg , refl , refl)) {x ∷ xs} {y} qxy | CommonConditions.just pxx qyy | just (x′ , y′) with backward-validity(bxfold-conditioned P Q (bxalg , refl , refl)) {xs} {y′} qyy
... | eq-length , cond = (cong suc eq-length) , pxx ∷ cond
forward-validity (bxfold-conditioned _ _ (bxalg , refl , refl)) {[]} (refl , []) = forward-validity bxalg CommonConditions.nothing
forward-validity (bxfold-conditioned P Q (bxalg , refl , refl)) {x ∷ xs} (refl , pxx ∷ ptwise) = forward-validity bxalg (CommonConditions.just pxx (forward-validity (bxfold-conditioned P Q (bxalg , refl , refl)) {xs} (refl , ptwise)))
conditioned-get-put (bxfold-conditioned _ _ (bxalg , refl , refl)) {[]} (refl , []) with conditioned-get-put bxalg {nothing} CommonConditions.nothing
... | gp-eq rewrite gp-eq = refl
conditioned-get-put (bxfold-conditioned P Q (bxalg , refl , refl)) {x ∷ xs} (refl , pxx ∷ ptwise) with conditioned-get-put bxalg {just (x , foldr (λ a b → get bxalg (just (a , b))) (get bxalg nothing) xs)} (CommonConditions.just pxx (forward-validity (bxfold-conditioned P Q (bxalg , refl , refl)) {xs} (refl , ptwise)))
... | gp-eq rewrite gp-eq | conditioned-get-put (bxfold-conditioned P Q (bxalg , refl , refl)) {xs} (refl , ptwise) = refl
conditioned-put-get (bxfold-conditioned P Q (bxalg , refl , refl)) {[]} {y} qxy with conditioned-put-get bxalg {nothing} {y} qxy
... | pg-eq with backward-validity bxalg qxy
... | cond with put bxalg nothing y
conditioned-put-get (bxfold-conditioned P Q (bxalg , refl , refl)) {[]} {y} qxy | pg-eq | CommonConditions.nothing | .nothing = pg-eq
conditioned-put-get (bxfold-conditioned P Q (bxalg , refl , refl)) {x ∷ xs} {y} qxy with conditioned-put-get bxalg {just (x , foldr (λ a b → get bxalg (just (a , b))) (get bxalg nothing) xs)} {y} qxy
... | pg-eq with backward-validity bxalg qxy
... | cond with put bxalg (just (x , foldr (λ a b → get bxalg (just (a , b))) (get bxalg nothing) xs)) y
conditioned-put-get (bxfold-conditioned P Q (bxalg , refl , refl)) {x ∷ xs} {y} qxy | pg-eq | CommonConditions.just pxx qyy | just (x′ , y′) rewrite conditioned-put-get (bxfold-conditioned P Q (bxalg , refl , refl)) {xs} {y′} qyy = pg-eq



bfilter-alg : {A : Set} →
              {- (P : A → A → Set) → -}
              (p : A → Bool) →
              Lens (Maybe (A × List A)) (List A)
get (bfilter-alg p) nothing = []
get (bfilter-alg p) (just (x , xs)) = if p x then x ∷ xs else xs
put (bfilter-alg p) nothing [] = nothing
put (bfilter-alg p) (just (x , xs)) (x′ ∷ xs′) = if p x then just (x′ , xs′) else just (x , x′ ∷ xs′)
put (bfilter-alg p) (just (x , xs)) [] = if p x then nothing else just (x , [])
put (bfilter-alg p) _ _ = nothing -- catch all case, failed branch
P (bfilter-alg p) = CommonConditions.lift CommonConditions.true-cond (CommonConditions.filter-cond CommonConditions.true-cond p)
Q (bfilter-alg p) = CommonConditions.filter-cond CommonConditions.true-cond p
backward-validity(bfilter-alg p) {just (x , xs)} {[]} (eq-len , ptwise) with p x
backward-validity(bfilter-alg p) {just (x , .[])} {[]} (refl , []) | false = CommonConditions.just tt (refl , [])
backward-validity(bfilter-alg p) {just (x , xs)} {x′ ∷ xs′} (eq-len , ptwise) with p x
backward-validity(bfilter-alg p) {just (x , xs)} {x′ ∷ xs′} (eq-len , ((pxx , _) ∷ ptwise)) | true = CommonConditions.just pxx (suc-injective eq-len , ptwise)
backward-validity(bfilter-alg p) {just (x , x₁ ∷ xs)} {x′ ∷ xs′} (eq-len , ((pxx , snd) ∷ ptwise)) | false = CommonConditions.just tt (eq-len , ((tt , snd) ∷ ptwise))
backward-validity(bfilter-alg p) {nothing} {[]} (eq-len , ptwise) = CommonConditions.nothing
forward-validity (bfilter-alg p) CommonConditions.nothing = refl , []
forward-validity (bfilter-alg p) {just (x , y)} (CommonConditions.just tt (refl , ptwise)) with p x Data.Bool.≟ true
... | yes eq rewrite eq = refl , (tt , eq) ∷ ptwise
... | no neq with p x
... | false = refl , ptwise
... | true = ⊥-elim (neq refl)
conditioned-get-put (bfilter-alg p) {just (x , xs)} (CommonConditions.just tt (refl , ptwise)) with p x Data.Bool.≟ true
... | yes eq rewrite eq | eq = refl
... | no neq with b≢true⇒b≡false (p x) neq
conditioned-get-put (bfilter-alg p) {just (x , [])} (CommonConditions.just tt (refl , ptwise)) | no neq | eq rewrite eq | eq = refl
conditioned-get-put (bfilter-alg p) {just (x , x₁ ∷ xs)} (CommonConditions.just tt (refl , ptwise)) | no neq | eq rewrite eq | eq = refl
conditioned-get-put (bfilter-alg p) CommonConditions.nothing = refl
conditioned-put-get (bfilter-alg p) {just (x , xs)} {[]} (eq-len , ptwise) with p x Data.Bool.≟ true
... | yes eq rewrite eq = refl
... | no neq with b≢true⇒b≡false (p x) neq
... | eq rewrite eq | eq = refl
conditioned-put-get (bfilter-alg p) {just (x , xs)} {x′ ∷ xs′} (eq-len , ptwise) with p x Data.Bool.≟ true
conditioned-put-get (bfilter-alg p) {just (x , xs)} {x′ ∷ xs′} (eq-len , ptwise) | yes eq with p x | eq
conditioned-put-get (bfilter-alg p) {just (x , xs)} {x′ ∷ xs′} (eq-len , ((_ , eq′) ∷ ptwise)) | yes eq | true | refl rewrite eq′ = refl
conditioned-put-get (bfilter-alg p) {just (x , xs)} {x′ ∷ xs′} (eq-len , ptwise) | no neq with b≢true⇒b≡false (p x) neq
... | eq rewrite eq | eq = refl
conditioned-put-get (bfilter-alg p) {nothing} {.[]} (fst , []) = refl


bfilter : {A : Set} →
          (A → Bool) →
          Lens (List A) (List A)
bfilter p = bxfold-conditioned CommonConditions.true-cond (CommonConditions.filter-cond CommonConditions.true-cond p) ((bfilter-alg p) , refl , refl)

{-# TERMINATING #-}
bxfold : ∀ {S : Set} {V : Set} →
         (bxalg-data : Σ (Lens (Maybe (S × V)) V) λ l → l hasConditions (λ _ _ → ⊤) and (λ _ _ → ⊤)) →
         Lens (List S) V
bxfold {S} {V} bxalg-data = record
                               { get = g
                               ; put = p
                               ; P = λ _ _ → ⊤
                               ; Q = λ _ _ → ⊤
                               ; backward-validity = λ {a} {b} _ → tt
                               ; forward-validity = λ {a} _ → tt
                               ; conditioned-get-put =  λ { tt → cgp }
                               ; conditioned-put-get =  λ { {as} {b} tt → cpg {as} {b}}
                               }
                               where
                                   bxalg : Lens (Maybe (S × V)) V
                                   bxalg = proj₁ bxalg-data
                                   g : List S → V
                                   g = foldr (λ { a b → get bxalg (just (a , b)) }) (get bxalg nothing)
                                   p : List S → V → List S
                                   p [] b = unfold′ (put bxalg nothing) b
                                   p (a ∷ as) b with put bxalg (just (a , g as)) b
                                   ... | just (a' , b') = a' ∷ p as b'
                                   ... | nothing        = []
                                   cgp : ∀ {as : List S} → p as (g as) ≡ as
                                   cgp {[]} with get-put-law-from-lens-data bxalg-data {nothing} tt
                                   ... | gp-eq rewrite gp-eq = refl
                                   cgp {a ∷ as} with get-put-law-from-lens-data bxalg-data {just (a , g as)} tt
                                   ... | gp-eq with put bxalg (just (a , g as)) (g (a ∷ as))
                                   cgp {a ∷ as} | refl
                                                | just (.a ,
                                                       .(foldr
                                                         (λ a₁ b →
                                                           get (proj₁ bxalg-data) (just (a₁ , b)))
                                                         (get (proj₁ bxalg-data) nothing) as))
                                       = cong₂ _∷_ refl (cgp {as})
                                   cgp {a ∷ as} | () | nothing
                                   cpg : ∀ {as : List S} {b : V} →
                                         g (p as b) ≡ b
                                   cpg {[]} {b} with put-get-law-from-lens-data bxalg-data {nothing} {b} tt
                                   ... | pg-eq with put bxalg nothing b
                                   ... | just (a , b') rewrite cpg {[]} {b'} | pg-eq = refl
                                   ... | nothing       = pg-eq
                                   cpg {a ∷ as} {b} with put-get-law-from-lens-data bxalg-data {just (a , g as)} {b} tt
                                   ... | pg-eq with put bxalg (just (a , g as)) b
                                   ... | just (a' , b') rewrite cpg {as} {b'} | pg-eq = refl
                                   ... | nothing        = pg-eq




blistf : ∀ {A B C : Set} →
             B →
             Σ (Lens B C) (λ l → l hasConditions (λ _ _ → ⊤) and (λ _ _ → ⊤)) →
             Lens (Maybe (A × B)) (Maybe (A × C))
blistf {A} {B} {C} default (l , l-conds) = record
                                 { get = λ { (just (a , b)) → just (a , get l b)
                                           ; nothing → nothing }
                                 ; put = λ { (just (a , b)) (just (a' , c)) → just (a' , put l b c)
                                            ; nothing (just (a , c)) → just (a , put l default c)
                                            ; (just _) nothing → nothing
                                            ; nothing nothing → nothing }
                                 ; P = λ _ _ → ⊤
                                 ; Q = λ _ _ → ⊤
                                 ; backward-validity = λ {a} {b} _ → tt
                                 ; forward-validity = λ {a} _ → tt
                                 ; conditioned-get-put = λ { {just (a , b)} tt → cong (λ b → just (a , b)) gp
                                                           ; {nothing} tt → refl }
                                 ; conditioned-put-get = λ { {just (a , b)} {just (a' , c)} tt → cong (λ c → just (a' , c)) pg
                                                           ; {nothing} {just (a , c)} tt → cong (λ c → just (a , c)) pg
                                                           ; {just _} {nothing} tt → refl
                                                           ; {nothing} {nothing} tt → refl }
                                 }
                                 where gp : ∀ {b : B} → put l b (get l b) ≡ b
                                       gp = get-put-law-from-lens-data (l , l-conds) tt
                                       pg : ∀ {b : B} {c : C} → get l (put l b c) ≡ c
                                       pg = put-get-law-from-lens-data (l , l-conds) tt



blistf′ : ∀ {S V T : Set} →
          (ct : T → T → Set) →
          (cs : S → S → Set) →
          (cv : V → V → Set) →
          Σ (Lens S V) (λ l → l hasConditions cs and cv) →
          Lens (Maybe (T × S)) (Maybe (T × V))
get (blistf′ {S} {V} {T} ct cs cv (l , l-conds)) (just (a , b)) = just (a , get l b)
get (blistf′ {S} {V} {T} ct cs cv (l , l-conds)) nothing        = nothing
put (blistf′ {S} {V} {T} ct cs cv (l , l-conds)) (just (a , b)) (just (a' , c)) = just (a' , put l b c)
put (blistf′ {S} {V} {T} ct cs cv (l , l-conds)) _              _               = nothing
P (blistf′ {S} {V} {T} ct cs cv (l , l-conds)) = CommonConditions.lift ct cs
Q (blistf′ {S} {V} {T} ct cs cv (l , l-conds)) = CommonConditions.lift ct cv
backward-validity (blistf′ {S} {V} {T} ct cs cv (l , l-conds)) {nothing} {.nothing} CommonConditions.nothing = CommonConditions.nothing
backward-validity (blistf′ {S} {V} {T} ct .(P l) .(Q l) (l , refl , refl)) {just x} {.(just (_ , _))} (CommonConditions.just x₁ x₂) = CommonConditions.just x₁ (backward-validity l x₂)
forward-validity (blistf′ {S} {V} {T} ct cs cv (l , l-conds)) {nothing} cond = CommonConditions.nothing
forward-validity (blistf′ {S} {V} {T} ct .(P l) .(Q l) (l , refl , refl)) {just .(_ , _)} (CommonConditions.just x x₁) = CommonConditions.just x (forward-validity l x₁)
conditioned-get-put (blistf′ {S} {V} {T} ct cs cv (l , l-conds)) {nothing} cond = refl
conditioned-get-put (blistf′ {S} {V} {T} ct .(P l) .(Q l) (l , refl , refl)) {just .(_ , _)} (CommonConditions.just x x₁) = cong just (cong₂ _,_ refl (conditioned-get-put l x₁)) 
conditioned-put-get (blistf′ {S} {V} {T} ct cs cv (l , l-conds)) {nothing} {.nothing} CommonConditions.nothing = refl
conditioned-put-get (blistf′ {S} {V} {T} ct .(P l) .(Q l) (l , refl , refl)) {just x} {.(just (_ , _))} (CommonConditions.just x₁ x₂) = cong just (cong₂ _,_ refl (conditioned-put-get l x₂))


bmapf : ∀ {A B C : Set} →
               A → C →
               Σ (Lens A B) (λ l → l hasConditions (λ _ _ → ⊤) and (λ _ _ → ⊤)) →
               Lens (Maybe (A × C)) (Maybe (B × C))
bmapf {A} {B} {C} a₀ c₀ (l , l-conds)
  = record
      { get = λ { (just (a , c)) → just (get l a , c)
                ; nothing        → nothing }
      ; put = λ { (just (a , c)) (just (b , c')) → just (put l a b , c')
                ; (just (a , c)) nothing         → nothing
                ; nothing (just (b , c))         → just (put l a₀ b , c)
                ; nothing nothing                → nothing }
      ; P = CommonConditions.keep-form c₀
      ; Q = CommonConditions.keep-form c₀
      ; backward-validity = λ { {just (a , c)} {just (b , c')} → λ z → z
                                  ; {just (a , c)} {nothing} → λ z → z
                                  ; {nothing} {just (b , c')} → λ _ → tt
                                  ; {nothing} {nothing} → λ _ → tt }
      ; forward-validity = λ { {just (a , c)} → λ _ z → z ; {nothing} → λ _ → tt }
      ; conditioned-get-put = λ { {just (a , b)} _ → cong just (cong₂ _,_ (get-put-law-from-lens-data (l , l-conds) tt) refl)
                                ; {nothing} _ → refl }
      ; conditioned-put-get = λ { {just (a , c)} {just (b , c')} _ → cong just (cong₂ _,_ (put-get-law-from-lens-data (l , l-conds) tt) refl)
                                ; {just (a , c)} {nothing} _ → refl
                                ; {nothing} {just (b , c)} _ → cong just (cong₂ _,_ (put-get-law-from-lens-data (l , l-conds) tt) refl)
                                ; {nothing} {nothing} _ → refl}
      }

bmapf′ : ∀ {S V T : Set} →
         (cs : S → S → Set) →
         (cv : V → V → Set) →
         (ct : T → T → Set) →
         Σ (Lens S V) (λ l → l hasConditions cs and cv) →
         Lens (Maybe (S × T)) (Maybe (V × T))
get (bmapf′ _ _ _ (l , _)) (just (a , c)) = just (get l a , c)
get (bmapf′ _ _ _ (l , _)) nothing        = nothing
put (bmapf′ _ _ _ (l , _)) (just (a , c)) (just (b , c')) = just (put l a b , c')
put (bmapf′ _ _ _ (l , _)) (just (a , c)) nothing         = nothing -- absurd
put (bmapf′ _ _ _ (l , _)) nothing (just (_ , _))         = nothing -- absurd
put (bmapf′ _ _ _ (l , _)) nothing nothing                = nothing
P (bmapf′ cs _ ct _) = (CommonConditions.lift cs ct)
Q (bmapf′ _ cv ct _) = (CommonConditions.lift cv ct)
backward-validity(bmapf′ cs cv ct (l , l-conds)) {nothing} {nothing} _ = CommonConditions.nothing
backward-validity(bmapf′ cs cv ct (l , l-conds)) {nothing} {just x} ()
backward-validity(bmapf′ cs cv ct (l , l-conds)) {just x} {nothing} ()
backward-validity(bmapf′ .(P l) .(Q l) ct (l , refl , refl)) {just x} {just .(_ , _)} (CommonConditions.just x₁ x₂) = CommonConditions.just (backward-validity l x₁) x₂
forward-validity (bmapf′ cs _ ct _) {nothing} _ = CommonConditions.nothing
forward-validity (bmapf′ .(P l) _ ct (l , refl , refl)) {just .(_ , _)} (CommonConditions.just x x₁) = CommonConditions.just (forward-validity l x) x₁
conditioned-get-put (bmapf′ .(P l) .(Q l) ct (l , refl , refl)) {nothing} _ = refl
conditioned-get-put (bmapf′ .(P l) .(Q l) ct (l , refl , refl)) {just .(_ , _)} (CommonConditions.just x x₁) = cong just (cong₂ _,_ (conditioned-get-put l x) refl)
conditioned-put-get (bmapf′ .(P l) .(Q l) ct (l , refl , refl)) {nothing} {nothing} _ = refl
conditioned-put-get (bmapf′ .(P l) .(Q l) ct (l , refl , refl)) {nothing} {just x} ()
conditioned-put-get (bmapf′ .(P l) .(Q l) ct (l , refl , refl)) {just x} {nothing} ()
conditioned-put-get (bmapf′ .(P l) .(Q l) ct (l , refl , refl)) {just x} {just .(_ , _)} (CommonConditions.just x₁ x₂) = cong just (cong₂ _,_ (conditioned-put-get l x₁) refl)

bxmap : ∀ {S V : Set} →
        (l-data : Σ (Lens S V) λ l → l hasConditions (λ _ _ → ⊤) and (λ _ _ → ⊤)) →
        Lens (List S) (List V)
bxmap {S} {V} (l , l-conds)
  = record
      { get = map (get l)
      ; put = p
      ; P = λ xs xs′ → length xs ≡ length xs′
      ; Q = λ ys ys′ → length ys ≡ length ys′
      ; backward-validity = λ {a} {b} → prop₁ a b
      ; forward-validity = λ _ → refl
      ; conditioned-get-put = λ {a} _ → cgp a
      ; conditioned-put-get = λ {a} {b} → cpg a b
      }
  where
    p : List S → List V → List S
    p [] [] = []
    p [] (x ∷ bs) = []
    p (x ∷ as) [] = []
    p (x ∷ as) (y ∷ bs) = put l x y ∷ p as bs
    prop₁ : (a : List S) (b : List V) →
            length (map (get l) a) ≡ length b → length a ≡ length (p a b)
    prop₁ [] [] eq-length = refl
    prop₁ (x ∷ as) (y ∷ bs) eq-length = cong suc (prop₁ as bs (suc-injective eq-length))
    cgp : (a : List S) → p a (map (get l) a) ≡ a
    cgp [] = refl
    cgp (x ∷ as) rewrite get-put-law-from-lens-data (l , l-conds) {x} tt | cgp as = refl
    cpg : (a : List S) (b : List V) →
          length (map (get l) a) ≡ length b → map (get l) (p a b) ≡ b
    cpg [] [] eq-length = refl
    cpg (x ∷ as) (y ∷ bs) eq-length
      rewrite put-get-law-from-lens-data (l , l-conds) {x} {y} tt | cpg as bs (suc-injective eq-length) = refl

bxmap2 : ∀ {S V} →
         (cs : S → S → Set) →
         (cv : V → V → Set) →
         (l-data : Σ (Lens S V) λ l → l hasConditions cs and cv) →
         Lens (List S) (List V)
get (bxmap2 cs cv (l , _)) = map (get l)
put (bxmap2 cs cv (l , _)) [] [] = []
put (bxmap2 cs cv (l , _)) [] (x ∷ ys) = [] -- absurd
put (bxmap2 cs cv (l , _)) (x ∷ xs) [] = [] -- absurd
put (bxmap2 cs cv (l , l-conds)) (x ∷ xs) (x₁ ∷ ys) = put l x x₁ ∷ put (bxmap2 cs cv (l , l-conds)) xs ys
P (bxmap2 cs cv l-data) = CommonConditions.licond cs
Q (bxmap2 cs cv l-data) = CommonConditions.licond cv
backward-validity(bxmap2 cs cv (l , l-conds)) {[]} {.[]} (refl , []) = refl , []
backward-validity(bxmap2 .(P l) .(Q l) (l , refl , refl)) {x ∷ xs} {y ∷ ys} (fst , (x₁ ∷ snd)) with backward-validity(bxmap2 (P l) (Q l) (l , refl , refl)) {xs} {ys} ((suc-injective fst) , snd)
... | (eq , ptwise) = cong suc eq , (backward-validity l x₁ ∷ ptwise)
forward-validity (bxmap2 cs cv l-data) {[]} cond = refl , []
forward-validity (bxmap2 .(P l) .(Q l) (l , refl , refl)) {x ∷ xs} (fst , (x₁ ∷ snd)) with forward-validity (bxmap2 (P l) (Q l) (l , refl , refl)) {xs} (refl , snd)
... | (eq , ptwise) = refl  ,  forward-validity l x₁ ∷ ptwise
conditioned-get-put (bxmap2 .(P l) .(Q l) (l , refl , refl)) {[]} cond = refl
conditioned-get-put (bxmap2 .(P l) .(Q l) (l , refl , refl)) {x ∷ xs} (fst , (x₁ ∷ snd)) with conditioned-get-put (bxmap2 (P l) (Q l) (l , refl , refl)) {xs} (refl , snd)
... | eq rewrite eq | conditioned-get-put l x₁ = refl
conditioned-put-get (bxmap2 .(P l) .(Q l) (l , refl , refl)) {[]} {[]} (refl , []) = refl
conditioned-put-get (bxmap2 .(P l) .(Q l) (l , refl , refl)) {x ∷ xs} {y ∷ ys} (fst , (x₁ ∷ snd)) with conditioned-put-get (bxmap2 (P l) (Q l) (l , refl , refl)) {xs} {ys} (suc-injective fst , snd)
... | eq rewrite eq | conditioned-put-get l x₁ = refl
               



bxfold′ : ∀ {S : Set} {V : Set} →
         (bxalg-data
           : Σ (Lens (Maybe (S × V)) V) λ l → l hasConditions CommonConditions.keep-form (get l nothing)
                                                and           (λ _ _ → ⊤)) →
         Lens (List S) V
bxfold′ {S} {V} (bxalg , bxalg-conds) = record
                               { get = g
                               ; put = p
                               ; P = λ as as′ → length as ≡ length as′
                               ; Q = λ b b′ → b ≡ b₀ → b′ ≡ b₀
                               ; backward-validity = λ {a} {b} → prop₁ a b
                               ; forward-validity = λ {a} _ z → z
                               ; conditioned-get-put = λ {a} _ → cgp
                               ; conditioned-put-get = λ {a} {b} → cpg a b
                               }
                               where
                                   -- bxalg : Lens (Maybe (S × V)) V
                                   -- bxalg = proj₁ bxalg-data
                                   b₀ = get bxalg nothing
                                   g : List S → V
                                   g = foldr (λ { a b → get bxalg (just (a , b)) }) (get bxalg nothing)
                                   p : List S → V → List S
                                   p [] b = unfold′ (put bxalg nothing) b
                                   p (a ∷ as) b with put bxalg (just (a , g as)) b
                                   ... | just (a' , b') = a' ∷ p as b'
                                   ... | nothing        = []
                                   prop₁ : ∀ s v →
                                           (g s ≡ b₀ → v ≡ b₀) →
                                           length s ≡ length (p s v)
                                   prop₁ [] v cond
                                     rewrite cond refl
                                           | get-put-law-from-lens-data (bxalg , bxalg-conds) {nothing} tt = refl
                                   prop₁ (x ∷ xs) v cond
                                     with change-transformation-from-lens-data
                                            (bxalg , bxalg-conds) {just (x , g xs)} {v} tt
                                   ... | sc with put bxalg (just (x , g xs)) v
                                   prop₁ (x ∷ xs) v cond | sc | just (x′ , y) = cong suc (prop₁ xs y sc)
                                   cgp : ∀ {as : List S} → p as (g as) ≡ as
                                   cgp {[]}
                                     with get-put-law-from-lens-data (bxalg , bxalg-conds) {nothing} tt
                                   ... | gp-eq rewrite gp-eq = refl
                                   cgp {a ∷ as}
                                     with get-put-law-from-lens-data
                                            (bxalg , bxalg-conds) {just (a , g as)} (λ z → z)
                                   ... | gp-eq with put bxalg (just (a , g as)) (g (a ∷ as))
                                   cgp {a ∷ as} | refl
                                                | just (.a
                                                       , .(foldr
                                                           (λ a₁ b →
                                                             get bxalg (just (a₁ , b)))
                                                           (get bxalg nothing) as)) = cong₂ _∷_ refl (cgp {as})
                                   cgp {a ∷ as} | () | nothing
                                   cpg : ∀ as b →
                                          (g as ≡ b₀ → b ≡ b₀) →
                                          g (p as b) ≡ b
                                   cpg [] b cond with b | cond refl
                                   ... | .b₀ | refl
                                     rewrite get-put-law-from-lens-data (bxalg , bxalg-conds) {nothing} tt = refl
                                   cpg (a ∷ as) b cond
                                     with put-get-law-from-lens-data (bxalg , bxalg-conds) {just (a , g as)} {b} tt
                                   ... | pg-eq
                                     with change-transformation-from-lens-data
                                            (bxalg , bxalg-conds) {just (a , g as)} {b} tt
                                   ... | sc with put bxalg (just (a , g as)) b
                                   ... | just (a' , b') rewrite cpg as b' sc | pg-eq = refl
                                   ... | nothing = pg-eq

bxmax′ : Lens (Maybe (ℤω × ℤω)) ℤω
bxmax′ = record
            { get = g
            ; put = p
            ; P = CommonConditions.keep-form -∞
            ; Q = λ _ _ → ⊤
            ; backward-validity = λ {a} {b} _ → prop₁ a b
            ; forward-validity = λ {a} _ → tt
            ; conditioned-get-put = λ {a} → cgp a
            ; conditioned-put-get = λ {a} {b} _ → cpg a b
            }
  where
    g : Maybe (ℤω × ℤω) → ℤω
    g nothing = -∞
    g (just (x , y)) = x ℤω.⊔ y
    p : Maybe (ℤω × ℤω) → ℤω → Maybe (ℤω × ℤω)
    p nothing v with v ℤω.≟ -∞
    p nothing v | yes p = nothing
    p nothing v | no ¬p = just (v , -∞)
    p (just (x , y)) v with y ℤω.≤? x
    ... | no x<y = just (v ℤω.⊓ x , v)
    ... | yes y≤x = just (v , v ℤω.⊓ y)
    prop₁ : (a : Maybe (ℤω × ℤω)) (b : ℤω) →
            CommonConditions.keep-form -∞ a (p a b)
    prop₁ nothing v with v ℤω.≟ -∞
    ... | yes eq = tt
    ... | no neq = tt
    prop₁ (just (x , y)) v with y ℤω.≤? x
    ... | yes y≤x = λ { refl → z⊓-∞≡-∞ v }
    ... | no x<y = λ { refl → ⊥-elim (x<y -∞≤any) }
    cgp : ∀ a →
          CommonConditions.keep-form -∞ a a → p a (g a) ≡ a
    cgp nothing cond = refl
    cgp (just (x , y)) _ with y ℤω.≤? x
    ... | yes y≤x = cong just
                         (cong₂ _,_
                                (Data.IntegerOmega.Properties.i≥j⇒i⊔j≡i y≤x)
                                (Data.IntegerOmega.Properties.i≥j⇒i⊓j≡j (Data.IntegerOmega.Properties.i≤j⊔i x y)))
    ... | no x<y = cong just
                        (cong₂ _,_
                               (Data.IntegerOmega.Properties.i≥j⇒i⊓j≡j (Data.IntegerOmega.Properties.i≤i⊔j x y))
                               (Data.IntegerOmega.Properties.i≤j⇒i⊔j≡j (Data.IntegerOmega.Properties.<⇒≤( Data.IntegerOmega.Properties.≰⇒> x<y))))
    cpg : (a : Maybe (ℤω × ℤω)) (b : ℤω) → g (p a b) ≡ b
    cpg nothing v with v ℤω.≟ -∞
    ... | yes eq = sym eq
    ... | no neq = ⊔-identityʳ v
    cpg (just (x , y)) v with y ℤω.≤? x
    ... | yes y≤x = Data.IntegerOmega.Properties.i≥j⇒i⊔j≡i (Data.IntegerOmega.Properties.i⊓j≤i v y)
    ... | no x<y = Data.IntegerOmega.Properties.i≤j⇒i⊔j≡j (Data.IntegerOmega.Properties.i⊓j≤i v x)


bxmaximum′ : Lens (List ℤω) ℤω
bxmaximum′ = bxfold′ (bxmax′ , refl , refl)


bxfold-map-fusion′ : ∀ {S V T} →
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
bxfold-map-fusion′ .(P l) .(Q l) .(Q bxalg) (l , refl , refl) (bxalg , fst , refl)
  = (λ {s} {s′} → refl)
  , ((λ {v} {v′} → refl)
  , ((λ {s} → get-eq s)
  , λ {s} {v} → put-eq s v))
  where
    l₁ = bxmap2 (P l) (Q l) (l , refl , refl) ； bxfold-conditioned (Q l) (Q bxalg) (bxalg , fst , refl) [ (λ z → z) , (λ z → z) ]
    l₂ = bxfold-conditioned (P l) (Q bxalg) ((bmapf′ (P l) (Q l) (Q bxalg) (l , refl , refl) ； bxalg
                                                [ (λ {v} {v'} cond → transport′ (cong (λ pred → pred v v') fst) cond)
                                                , ((λ {v} {v'} cond → transport′ (sym (cong (λ pred → pred v v') fst) ) cond)) ])
                                                , refl , refl)
    get-eq : ∀ s → get l₁ s ≡ get l₂ s
    get-eq [] = refl
    get-eq (x ∷ xs) rewrite get-eq xs = refl
    put-eq : ∀ s v → Q bxalg (get l₁ s) v →
             put l₁ s v ≡ put l₂ s v
    put-eq [] ys cond
      with put bxalg nothing ys
    ... | nothing = refl
    ... | just x = refl
    put-eq (x ∷ xs) ys cond with get l₁ xs | get-eq xs
    ... | .(get l₂ xs) | refl
      with transport′ (cong (λ pred → pred (just (get l x , get l₂ xs)) (put bxalg (just (get l x , get l₂ xs)) ys)) fst) (backward-validity bxalg cond)
    ... | cond' with put bxalg (just (get l x , get l₂ xs)) ys
    put-eq (x ∷ xs) ys cond | .(foldr _ (get bxalg nothing) xs) | refl | CommonConditions.just x₁ x₂ | just (y , z) with put-eq xs z
    ... | eq-pre rewrite sym (get-eq xs) | eq-pre x₂ = refl




bxfold-map-fusion : ∀ {A B C : Set} →
                    (a₀ : A) →
                    (l-data : Σ (Lens A B) (λ l → l hasConditions (λ _ _ → ⊤) and (λ _ _ → ⊤))) →
                    (bxalg₁-data
                      : Σ (Lens (Maybe (B × C)) C) λ l → l hasConditions CommonConditions.keep-form (get l nothing)
                                                           and           (λ _ _ → ⊤)) →
                    (bxalg₂-data
                      : Σ (Lens (Maybe (A × C)) C) λ l → l hasConditions CommonConditions.keep-form (get l nothing)
                                                           and           (λ _ _ → ⊤)) →
                    (eq : get (proj₁ bxalg₁-data) nothing ≡ get (proj₁ bxalg₂-data) nothing) →
                    (inner-fuse :
                      bmapf a₀ (get (proj₁ bxalg₁-data) nothing) l-data ； proj₁ bxalg₁-data
                        [ (λ {v} {v'} cond →
                            transport′ (cong (λ pred → pred v v')
                                             (proj₁ (proj₂ bxalg₁-data))) cond)
                        , (λ {v} {v'} cond →
                             transport′ (sym (cong (λ pred → pred v v')
                                                   (proj₁ (proj₂ bxalg₁-data)))) cond) ]
                    ≈
                      proj₁ bxalg₂-data) →
                      bxmap l-data ； bxfold′ bxalg₁-data [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ]
                    ≈
                      bxfold′ bxalg₂-data
bxfold-map-fusion {A} {B} {C} a₀ (l , l-conds) (bxalg₁ , bxalg₁-conds) (bxalg₂ , bxalg₂-conds) base-eq (P-eq , Q-eq , get-eq , put-eq)
  = (λ {s} {s′} → refl)
  , (λ {v} {v′} → Q-eq′ v v′ )
  , (λ {s} → get-eq′ s)
  , λ {s} {v} → put-eq′ s v
  where
    ℓ₁ = bxmap (l , l-conds) ； bxfold′ (bxalg₁ , bxalg₁-conds) [ (λ {v} {v'} z → z) , (λ {v} {v'} z → z) ]
    ℓ₂ = bxfold′ (bxalg₂ , bxalg₂-conds)
    Q-eq′ : ∀ v v′ → Q ℓ₁ v v′ ≡ Q ℓ₂ v v′
    Q-eq′ v v′ rewrite base-eq = refl
    get-eq′ : ∀ s →
              get ℓ₁ s ≡ get ℓ₂ s
    get-eq′ [] = base-eq
    get-eq′ (x ∷ xs) rewrite get-eq′ xs | get-eq {just (x , get ℓ₂ xs)} = refl
    put-eq′ : ∀ s v →
              (get ℓ₁ s ≡ get bxalg₁ nothing → v ≡ get bxalg₁ nothing) →
              put ℓ₁ s v ≡ put ℓ₂ s v
    put-eq′ [] y cond
      with put bxalg₁ nothing y
         | cong (put bxalg₁ nothing) (cond refl)
         | put bxalg₂ nothing y
         | trans (cong (put bxalg₂ nothing) (cond refl)) (cong (put bxalg₂ nothing) base-eq)
    ... | .(put bxalg₁ nothing (get bxalg₁ nothing))
        | refl
        | .(put bxalg₂ nothing (get bxalg₂ nothing))
        | refl
        rewrite get-put-law-from-lens-data (bxalg₁ , bxalg₁-conds) {nothing} tt
              | get-put-law-from-lens-data (bxalg₂ , bxalg₂-conds) {nothing} tt = refl
    put-eq′ (x ∷ xs) y cond with get ℓ₁ xs | get-eq′ xs
    ... | .(get ℓ₂ xs) | refl
      with put-eq {just (x , get ℓ₂ xs)} {y}
                  (transport′ (cong (λ pred → pred (get bxalg₁ (just (get l x , get ℓ₂ xs))) y)
                                    (sym (proj₂ bxalg₁-conds))) tt)
    ... | p-eq
      with change-transformation-from-lens-data (bxalg₁ , bxalg₁-conds) {just (get l x , get ℓ₂ xs)} {y} tt
    ... | sc with put bxalg₁ (just (get l x , get ℓ₂ xs)) y | put bxalg₂ (just (x , get ℓ₂ xs)) y
    ... | nothing | nothing = refl
    put-eq′ (x ∷ xs) y cond
      | .(foldr _ (get bxalg₂ nothing) xs) | refl | refl | sc | just (a , b) | just (.(put l x a) , .b)
      = cong₂ _∷_ refl (put-eq′ xs b λ eq → sc (trans (sym (get-eq′ xs)) eq))




bxfold′-fusion : ∀ {S V T : Set} →
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
                 ( (proj₁ bxalg₁-data ； proj₁ l-data [ (λ {v} {v′} cvvv → transport′ (sym (cong (λ pred → pred v v′)  (proj₂ (proj₂ bxalg₁-data)))) (transport′ (cong (λ pred → pred v v′) (proj₁ (proj₂ l-data))) cvvv))
                                                      , (λ {v} {v′} cvvv → transport′ (sym (cong (λ pred → pred v v′)  (proj₁ (proj₂ l-data)))) (transport′ (cong (λ pred → pred v v′) (proj₂ (proj₂ bxalg₁-data))) cvvv)) ])
                 ≈ blistf′ cs cv ct l-data ； proj₁ bxalg₂-data [ (λ {v} {v′} cvv → transport′ (cong (λ pred → pred v v′) (proj₁ (proj₂ bxalg₂-data))) cvv)
                                                                , (λ {v} {v′} cvv → transport′ (cong (λ pred → pred v v′) (sym (proj₁ (proj₂ bxalg₂-data)))) cvv) ] ) →
                 bxfold-conditioned cs cv bxalg₁-data ； proj₁ l-data [ (λ {v} {v′} → transport′ (cong-app (cong-app (proj₁ (proj₂ l-data)) v) v′))
                                                                      , (λ {v} {v′} → transport′ (cong-app (cong-app (sym (proj₁ (proj₂ l-data))) v) v′)) ]
                 ≈ bxfold-conditioned cs ct bxalg₂-data
bxfold′-fusion cs .(P l) .(Q l) (bxalg₁ , cond₁ , refl) (l , refl , refl) (bxalg₂ , cond₂ , refl) (P-eq , Q-eq , get-fuse , put-fuse)
  = (λ {s} {s′} → refl)
  , (λ {v} {v′} → refl)
  , (λ {as} → get-fusion as)
  , λ {as} {t} q → put-fusion as t q
  where
    bx-abbr = bxfold-conditioned cs (P l) (bxalg₁ , cond₁ , refl) ； l [ (λ q → q) , (λ q → q) ]
    get-fusion : ∀ xs →
                 get l (get (bxfold-conditioned cs (P l) (bxalg₁ , cond₁ , refl)) xs)
                 ≡
                 get (bxfold-conditioned cs (Q l) (bxalg₂ , cond₂ , refl)) xs
    get-fusion [] = get-fuse {nothing}
    get-fusion (a ∷ as) rewrite sym (get-fusion as) = get-fuse {just (a , get (bxfold-conditioned cs (P l) (bxalg₁ , cond₁ , refl)) as)}
    put-fusion : ∀ as t → Q bx-abbr (get bx-abbr as) t →
                 put (bxfold-conditioned cs (P l) (bxalg₁ , cond₁ , refl)) as (put l (get (bxfold-conditioned cs (P l) (bxalg₁ , cond₁ , refl)) as) t)
                 ≡
                 put (bxfold-conditioned cs (Q l) (bxalg₂ , cond₂ , refl)) as t
    put-fusion [] t cond with get-fuse {nothing} | put-fuse {nothing} {t} cond
    ... | gf | pf with put bxalg₁ nothing (put l (get bxalg₁ nothing) t)
    put-fusion [] t cond | gf | refl | .nothing with backward-validity bxalg₂ {nothing} {t} (transport′ (cong (λ x → Q bxalg₂ x t) gf) cond)
    ... | cvalg₂ with transport′ (cong (λ pred → pred nothing (put bxalg₂ nothing t)) cond₂) cvalg₂
    ... | cond₃ with put bxalg₂ nothing t
    put-fusion [] t cond | gf | refl | .nothing | cvalg₂ | CommonConditions.nothing | .nothing = refl
    put-fusion (a ∷ as) t cond with get-fuse {just (a , get (bxfold-conditioned cs (P l) (bxalg₁ , cond₁ , refl)) as) } | put-fuse {just (a , get (bxfold-conditioned cs (P l) (bxalg₁ , cond₁ , refl)) as)} {t} cond | get-fusion as
    ... | gf | pf | gf-rec with backward-validity bxalg₂ {just (a , get l (get (bxfold-conditioned cs (P l) (bxalg₁ , cond₁ , refl)) as))} {t} (transport′ (cong (λ x → Q bxalg₂ x t) gf) cond)
    ... | cvalg₂ with transport′ (cong (λ pred → pred (just (a , get l (get (bxfold-conditioned cs (P l) (bxalg₁ , cond₁ , refl)) as))) (put bxalg₂ (just (a , get l (get (bxfold-conditioned cs (P l) (bxalg₁ , cond₁ , refl)) as))) t)) cond₂) cvalg₂
    ... | cond₃ with get (bxfold-conditioned cs (Q l) (bxalg₂ , cond₂ , refl)) as
    put-fusion (a ∷ as) t cond | gf | pf | refl | cvalg₂ | cond₃ | .(get l (get (bxfold-conditioned cs (P l) (bxalg₁ , cond₁ , refl)) as)) with put bxalg₁ (just (a , get (bxfold-conditioned cs (P l) (bxalg₁ , cond₁ , refl)) as)) (put l (get bxalg₁ (just (a , get (bxfold-conditioned cs (P l) (bxalg₁ , cond₁ , refl)) as))) t) |  put bxalg₂ (just (a , get l (get (bxfold-conditioned cs (P l) (bxalg₁ , cond₁ , refl)) as))) t
    put-fusion (a ∷ as) t cond | gf | refl | refl | cvalg₂ | CommonConditions.just x₁ x₂ | .(get l (foldr _ (get bxalg₁ nothing) as)) | just (x , .(put l (foldr (λ a₁ b → get bxalg₁ (just (a₁ , b))) (get bxalg₁ nothing) as) _)) | just (.x , y′) = cong₂ _∷_ refl (put-fusion as y′ x₂)



{-# TERMINATING #-}
bxfold-fusion : ∀ {S : Set} {V T : Set} →                                                                  
                (l : Lens V T) →
                (l-conds : l hasConditions (λ _ _ → ⊤) and (λ _ _ → ⊤)) →
                {bxalg₁-data
                  : Σ (Lens (Maybe (S × V)) V) λ l → l hasConditions (λ _ _ → ⊤) and (λ _ _ → ⊤)} →
                {bxalg₂-data
                  : Σ (Lens (Maybe (S × T)) T) λ l → l hasConditions (λ _ _ → ⊤) and (λ _ _ → ⊤)} →
                 ( (proj₁ bxalg₁-data) ； l
                   [ (λ {v} {v'} _ → transport′ (sym (cong (λ pred → pred v v')  (proj₂ (proj₂ bxalg₁-data)))) tt)
                   , (λ {v} {v'} _ → transport′ (sym (cong (λ pred → pred v v')  (proj₁ l-conds))) tt) ] )
                ≈  ( blistf (get (proj₁ bxalg₁-data) nothing) (l , l-conds) ； (proj₁ bxalg₂-data)
                   [ (λ {v} {v'} _ → tt)
                   , (λ {v} {v'} _ → transport′ (sym (cong (λ pred → pred v v')  (proj₁ (proj₂ bxalg₂-data)))) tt) ] ) →
                ( bxfold bxalg₁-data  ； l
                  [ (λ {v} {v'} _ → tt) , (λ {v} {v'} _ → transport′ (sym (cong (λ pred → pred v v')
                                                                                (proj₁ l-conds))) tt) ] )
                ≈ ( bxfold bxalg₂-data )
bxfold-fusion {S} {V} {T} l l-conds {bxalg₁-data} {bxalg₂-data} (P-eq , Q-eq , get-fuse , put-fuse)
  = refl
  , (λ {v} {v′} → cong (λ pred → pred v v′) (proj₂ l-conds))
  , ((λ {as} → get-fusion {as}))
  , ((λ { {as} {c} q → put-fusion {as} {c}}))
    where
      bxalg₁ : Lens (Maybe (S × V))V
      bxalg₁ = proj₁ bxalg₁-data
      bxalg₂ : Lens (Maybe (S × T)) T
      bxalg₂ = proj₁ bxalg₂-data
      cons-alg₁ : S → V → V
      cons-alg₁ s v = get (proj₁ bxalg₁-data) (just (s , v))
      nil-alg₁ : V
      nil-alg₁ = get (proj₁ bxalg₁-data) nothing
      cons-alg₂ : S → T → T
      cons-alg₂ s t = get (proj₁ bxalg₂-data) (just (s , t))
      nil-alg₂ : T
      nil-alg₂ = get (proj₁ bxalg₂-data) nothing
      g₁ : List S → V
      g₁ = get (bxfold bxalg₁-data)
      g₂ : List S → T
      g₂ = get (bxfold bxalg₂-data)
      p₁ : List S → V → List S
      p₁ = put (bxfold bxalg₁-data)
      p₂ : List S → T → List S
      p₂ = put (bxfold bxalg₂-data)
      get-fusion : ∀ {as : List S} →
                   get l (g₁ as) ≡ g₂ as
      get-fusion {[]} = get-fuse {nothing}
      get-fusion {a ∷ as} rewrite sym (get-fusion {as}) = get-fuse {just (a , g₁ as)}
      put-fusion : ∀ {as : List S} {c : T} →
                   p₁ as (put l (g₁ as) c) ≡ p₂ as c
      put-fusion {[]} {c}
        with put-fuse {nothing} {c}
                      (transport′ (cong (λ pred → pred (get l (get bxalg₁ nothing)) c) (sym (proj₂ l-conds))) tt) 
      ... | pf
        with put bxalg₁ nothing (put l (get (proj₁ bxalg₁-data) nothing) c) | put bxalg₂ nothing c
      put-fusion {[]} {c}
        | refl | just (a' , .(put l (get (proj₁ bxalg₁-data) nothing) c'')) | just (.a' , c'')
        = cong₂ _∷_ refl (put-fusion {[]} {c''})
      ... | nothing | nothing = refl
      put-fusion {a ∷ as} {c}
        with put-fuse {just (a , g₁ as)} {c}
                      (transport′ (cong (λ pred → pred (get l (get bxalg₁ (just (a , g₁ as)))) c)
                                        (sym (proj₂ l-conds))) tt)
      ... | pf with g₂ as            | get-fusion {as}
      ...         | .(get l (g₁ as)) | refl
        with put bxalg₂ (just (a , get l (g₁ as))) c
           | put bxalg₁ (just (a , g₁ as)) (put l (get bxalg₁ (just (a , g₁ as))) c)
      put-fusion {a ∷ as} {c}
        | refl | .(get l (foldr _ (get (proj₁ bxalg₁-data) nothing) as)) | refl | just (a' , c')
        | just (.a' , .(put l (foldr (λ a₁ b → get (proj₁ bxalg₁-data) (just (a₁ , b)))
                              (get (proj₁ bxalg₁-data) nothing) as) c'))
        = cong₂ _∷_ refl (put-fusion {as} {c'})
      ... | nothing        | nothing          = refl
