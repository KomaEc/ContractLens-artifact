module TerminatingFold where

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
open import Util using (η-⊤; transport′; funext; funext'; case_of_)
open import Data.Maybe.Base using (just; nothing; maybe)
-- open import Data.Integer as ℤ renaming (suc to zsuc)
open import Induction.WellFounded
open import Data.Nat.Induction
open import Lens
open Lens.Lens

open import Core using (blistf)


unfold↓ : ∀ {A : Set} {B : ℕ → Set} →
         (coalg : ∃[ n ] B n → Maybe (A × ∃[ n ] B n)) →
         (terminating : ∀ {n} {b : B n} → coalg (n , b) ≡ nothing ⊎
                                          ∃[ a ] ∃[ m ] ∃[ b' ] (coalg (n , b) ≡ just (a , m , b') × m <′ n)) →
         ∀ {n} → B n → List A
unfold↓ {A} {B} coalg terminating {n} = <′-rec (λ n → B n → List A) step n 
  where
    step : (n : ℕ) → ((m : ℕ) → suc m ≤′ n → B m → List A) → B n → List A
    step n rec b with terminating {n} {b}
    step n rec b | inj₁ _ = []
    step n rec b | inj₂ (a , m , b' , _ , m<n) = a ∷ rec m m<n b'

Acc-<′-unique : ∀ n → (p q : Acc _<′_ n) → p ≡ q 
Acc-<′-unique n = <′-rec  (λ n → (p q : Acc _<′_ n) → p ≡ q) step n
  where step : (n : ℕ) → ((m : ℕ) → m <′ n → (p' q' : Acc _<′_ m) → p' ≡ q') → (p q : Acc _<′_ n) → p ≡ q
        step n rec (acc rs₁) (acc rs₂)
          = cong acc
                 (funext {f = rs₁} {g = rs₂}
                   (λ m →
                     funext {f = rs₁ m} {g = rs₂ m} λ m<′n → rec m m<′n (rs₁ m m<′n) (rs₂ m m<′n)))

unfold↓-computation : ∀ {A : Set} {B : ℕ → Set} →
                {coalg : ∃[ n ] B n → Maybe (A × ∃[ n ] B n)} →
                {terminating : ∀ {n} {b : B n} → coalg (n , b) ≡ nothing ⊎
                                                 ∃[ a ] ∃[ m ] ∃[ b' ] (coalg (n , b) ≡ just (a , m , b') × m <′ n)} →
                ∀ {n} {b : B n} {a : A} {m} {b' : B m} →
                coalg (n , b) ≡ just (a , m , b') →
                unfold↓ coalg terminating b ≡ a ∷ unfold↓ coalg terminating b'
unfold↓-computation {_}{_}{coalg}{terminating} {n} {b} {a} {m} {b'} eq with terminating {n} {b}
unfold↓-computation {_} {_} {coalg} {terminating} {n} {b} {a} {m} {b'} eq | inj₁ eq-nothing with trans (sym eq-nothing) eq
... | ()
unfold↓-computation {_} {_} {coalg} {terminating} {n} {b} {a'} {m'} {b''} eq | inj₂ (a , m , b' , eq-just , m<n)
  with trans (sym eq) eq-just
... | refl with <′-wellFounded′ n m m<n
... | acc rs with terminating {m} {b'}
... | inj₁ _ = refl
unfold↓-computation {_} {_} {coalg} {terminating} {n} {b} {.a} {.m} {.b'} eq
  | inj₂ (a , m , b' , eq-just , m<n) | refl | acc rs | inj₂ (a' , m' , b'' , eq-just' , m'<m)
  rewrite Acc-<′-unique m' (rs m' m'<m) (<′-wellFounded′ m m' m'<m) = refl 


bxfold : ∀ {S : Set} {V : ℕ → Set} →
         (bxalg-data
           : Σ (Lens (Maybe (S × ∃[ n ] V n)) (∃[ n ] V n)) λ l → l hasConditions (λ _ _ → ⊤) and (λ _ _ → ⊤)) →
         (terminating
           : ∀ {n} {b : V n} → put (proj₁ bxalg-data) nothing (n , b) ≡ nothing ⊎
                               ∃[ a ] ∃[ m ] ∃[ b' ]
                                 (put (proj₁ bxalg-data) nothing (n , b) ≡ just (a , m , b') × m <′ n)) →
         Lens (List S) (∃[ n ] V n)
bxfold {S} {V} bxalg-data terminating =
                         record
                             { get = g
                             ; put = p
                             ; P = λ _ _ → ⊤
                             ; Q = λ _ _ → ⊤
                             ; backward-validity = λ {a} {b} _ → tt
                             ; forward-validity = λ {a} _ → tt
                             ; conditioned-get-put = λ { tt → cgp }
                             ; conditioned-put-get = λ { {as} {n , b} tt → cpg {as} {n} {b}}
                             }
                             where
                                   bxalg : Lens (Maybe (S × ∃[ n ] V n)) (∃[ n ] V n)
                                   bxalg = proj₁ bxalg-data
                                   g : List S → ∃[ n ] V n
                                   g = foldr (λ { a (m , b) → get bxalg (just (a , m , b)) }) (get bxalg nothing)
                                   p : List S → ∃[ n ] V n → List S
                                   p [] (n , b) = unfold↓ (put bxalg nothing) terminating b
                                   p (a ∷ as) (n , b) with put bxalg (just (a , g as)) (n , b)
                                   p (a ∷ as) (n , b)    | just (a' , m , b') = a' ∷ p as (m , b')
                                   p (a ∷ as) (n , b)    | nothing = []
                                   cgp : ∀ {as : List S} → p as (g as) ≡ as
                                   cgp {[]} with get-put-law-from-lens-data bxalg-data {nothing} tt
                                   ... | gp-eq with g []
                                   cgp {[]} | gp-eq | n , b with terminating {n} {b}
                                   cgp {[]} | gp-eq | n , b | inj₁ eq-nothing = refl
                                   cgp {[]} | gp-eq | n , b | inj₂ (a , m , b' , eq-just , m<n) with trans (sym gp-eq) eq-just
                                   ... | ()
                                   cgp {a ∷ as} with get-put-law-from-lens-data bxalg-data {just (a , g as)} tt
                                   ... | gp-eq with put bxalg (just (a , g as)) (get bxalg (just (a , g as)))
                                   cgp {a ∷ as} | refl | just .(a , g as) = cong₂ _∷_ refl (cgp {as})
                                   cpg-nill : ∀  {n} {b : V n} →
                                          g (p [] (n , b)) ≡ (n , b)
                                   cpg-nill {n} {b} = <′-rec (λ n → (b : V n) → g (p [] (n , b)) ≡ (n , b)) step n b
                                     where
                                       step : (n : ℕ) →
                                                  ((m : ℕ) → suc m ≤′ n → (b' : V m) → g (p [] (m , b')) ≡ (m , b')) →
                                                  (b : V n) → g (p [] (n , b)) ≡ (n , b)
                                       step n rec b with put-get-law-from-lens-data bxalg-data {nothing} {n , b} tt
                                       ... | pg-eq with terminating {n} {b}
                                       step n rec b | pg-eq | inj₁ eq-nothing with put bxalg nothing (n , b)
                                       step .(proj₁ (get (proj₁ bxalg-data) nothing)) rec .(proj₂ (get (proj₁ bxalg-data) nothing))
                                         | refl | inj₁ refl | nothing = refl
                                       step n rec b | pg-eq | inj₂ (a , m , b' , eq-just , m<n) with <′-wellFounded′ n m m<n
                                       ... | acc rs
                                         with trans
                                               (cong (λ { (m , b') → get bxalg (just (a , m , b')) })
                                                     (rec m m<n b'))
                                               (trans (sym (cong (get bxalg) eq-just)) pg-eq)
                                       ... | rec-eq with terminating {m} {b'}
                                       ... | inj₁ eq-nothing = rec-eq
                                       ... | inj₂ (a' , m' , b'' , eq-just' , m'<m)
                                         rewrite Acc-<′-unique m' (rs m' m'<m) (<′-wellFounded′ m  m' m'<m)= rec-eq
                                   cpg : ∀ {as : List S} {n} {b : V n} →
                                         g (p as (n , b)) ≡ (n , b)
                                   cpg {[]} {n} {b} = cpg-nill {n} {b}
                                   cpg {a ∷ as} {n} {b} with put-get-law-from-lens-data bxalg-data {just (a , g as)} {n , b} tt
                                   ... | pg-eq with put bxalg (just (a , g as)) (n , b)
                                   ... | just (a' , m , b')
                                     = trans (cong (λ { (m , b') → get bxalg (just (a' , m , b'))}) (cpg {as} {m} {b'})) pg-eq
                                   ... | nothing = pg-eq


bxfold-fusion : ∀ {S : Set} {V T : ℕ → Set} →
                (l : Lens (∃[ n ] V n) (∃[ n ] T n)) →
                (l-conds : l hasConditions (λ _ _ → ⊤) and (λ _ _ → ⊤)) →
                {bxalg₁-data : Σ (Lens (Maybe (S × ∃[ n ] V n)) (∃[ n ] V n)) λ l → l hasConditions (λ _ _ → ⊤) and (λ _ _ → ⊤)} →
                {terminating₁ : ∀ {n} {b : V n} → put (proj₁ bxalg₁-data) nothing (n , b) ≡ nothing ⊎
                                ∃[ a ] ∃[ m ] ∃[ b' ] (put (proj₁ bxalg₁-data) nothing (n , b) ≡ just (a , m , b') × m <′ n)} →
                {bxalg₂-data : Σ (Lens (Maybe (S × ∃[ n ] T n)) (∃[ n ] T n)) λ l → l hasConditions (λ _ _ → ⊤) and (λ _ _ → ⊤)} →
                {terminating₂ : ∀ {n} {c : T n} → put (proj₁ bxalg₂-data) nothing (n , c) ≡ nothing ⊎
                                ∃[ a ] ∃[ m ] ∃[ c' ] (put (proj₁ bxalg₂-data) nothing (n , c) ≡ just (a , m , c') × m <′ n)} →
                 ( (proj₁ bxalg₁-data) ； l
                                     [ (λ {v} {v'} _ → transport′ (sym (cong (λ pred → pred v v')  (proj₂ (proj₂ bxalg₁-data)))) tt)
                                     , (λ {v} {v'} _ → transport′ (cong (λ pred → pred v v') (sym (proj₁ l-conds))) tt) ] )
                 ≈
                 ( blistf (get (proj₁ bxalg₁-data) nothing) (l , l-conds) ； (proj₁ bxalg₂-data)
                   [ (λ {v} {v'} _ → tt)
                   , (λ {v} {v'} _ → transport′ (cong (λ pred → pred v v') (sym (proj₁ (proj₂ bxalg₂-data)))) tt) ] ) →
                 ( bxfold bxalg₁-data terminating₁ ； l
                   [ (λ {v} {v'} _ → tt)
                   , ((λ {v} {v'} _ → transport′ (cong (λ pred → pred v v') (sym (proj₁ l-conds))) tt)) ] )
                 ≈
                 ( bxfold bxalg₂-data terminating₂ )
bxfold-fusion {S} {V} {T} l l-conds {bxalg₁-data} {terminating₁} {bxalg₂-data} {terminating₂} (P-eq , Q-eq , get-fuse , put-fuse)
  = refl
  , (λ {v} {v′} → cong (λ pred → pred v v′) (proj₂ l-conds))
  , ((λ {as} → get-fusion {as}))
  , ((λ { {as} {n , c} _ → put-fusion {as} {n} {c}}))
    where
      bxalg₁ : Lens (Maybe (S × ∃[ n ] V n)) (∃[ n ] V n)
      bxalg₁ = proj₁ bxalg₁-data
      bxalg₂ : Lens (Maybe (S × ∃[ n ] T n)) (∃[ n ] T n)
      bxalg₂ = proj₁ bxalg₂-data
      cons-alg₁ : S → (∃[ n ] V n) → (∃[ n ] V n)
      cons-alg₁ s v = get (proj₁ bxalg₁-data) (just (s , v))
      nil-alg₁ : ∃[ n ] V n
      nil-alg₁ = get (proj₁ bxalg₁-data) nothing
      cons-alg₂ : S → (∃[ n ] T n) → (∃[ n ] T n)
      cons-alg₂ s t = get (proj₁ bxalg₂-data) (just (s , t))
      nil-alg₂ : ∃[ n ] T n
      nil-alg₂ = get (proj₁ bxalg₂-data) nothing
      g₁ : List S → ∃[ n ] V n
      g₁ = get (bxfold bxalg₁-data terminating₁)
      g₂ : List S → ∃[ n ] T n
      g₂ = get (bxfold bxalg₂-data terminating₂)
      p₁ : List S → (∃[ n ] V n) → List S
      p₁ = put (bxfold bxalg₁-data terminating₁)
      p₂ : List S → (∃[ n ] T n) → List S
      p₂ = put (bxfold bxalg₂-data terminating₂)
      get-fusion : ∀ {as : List S} →
                   get l (g₁ as) ≡ g₂ as
      get-fusion {[]} = get-fuse {nothing}
      get-fusion {a ∷ as} with get-fusion {as}
      ...                    | rec rewrite sym rec = get-fuse {just (a , get (bxfold bxalg₁-data terminating₁) as )}
      put-fusion-nil : ∀ n → (c : T n) → p₁ [] (put l (g₁ []) (n , c)) ≡ p₂ [] (n , c)
      put-fusion-nil = <′-rec (λ n → (c : T n) → p₁ [] (put l (g₁ []) (n , c)) ≡ p₂ [] (n , c)) step
        where step : ∀ n →
                     (rec : ∀ m → m <′ n → (c' : T m) → p₁ [] (put l (g₁ []) (m , c')) ≡ p₂ [] (m , c')) →
                     (c : T n) → p₁ [] (put l (g₁ []) (n , c)) ≡ p₂ [] (n , c)
              step n rec c
                with put-fuse {nothing} {n , c}
                              (transport′ (cong (λ pred → pred (get l (get bxalg₁ nothing)) (n , c)) (sym (proj₂ l-conds))) tt)
              ... | pf with put l (get bxalg₁ nothing) (n , c)
              ... | m , b  with terminating₁ {b = b} | terminating₂ {c = c}
              step n rec c | pf | m , b | inj₁ eq-nothing₁ | inj₁ eq-nothing₂ = refl
              step n rec c | pf | m , b | inj₁ eq-nothing₁ | inj₂ (a , n' , c' , eq-just₂ , n'<n)
                with put (proj₁ bxalg₂-data) nothing (n , c)
              step n rec c | pf | m , b | inj₁ eq-nothing₁ | inj₂ (a , n' , c' , refl , n'<n) | .(just (a , n' , c'))
                with trans (sym pf) eq-nothing₁
              ... | ()
              step n rec c | pf | m , b | inj₂ (a , m' , b' , eq-just₁ , m'<m) | inj₁ eq-nothing₂
                with put (proj₁ bxalg₂-data) nothing (n , c)
              step n rec c | pf | m , b | inj₂ (a , m' , b' , eq-just₁ , m'<m) | inj₁ refl | .nothing
                with trans (sym pf) eq-just₁
              ... | () 
              step n rec c | pf | m , b | inj₂ (a , m' , b' , eq-just₁ , m'<m) | inj₂ (a' , n' , c' , eq-just₂ , n'<n)
                with put (proj₁ bxalg₁-data) nothing (m , b) | put (proj₁ bxalg₂-data) nothing (n , c)
              step n rec c
                | pf | m , b | inj₂ (a , m' , b' , refl , m'<m) | inj₂ (a' , n' , c' , refl , n'<n)
                | .(just (a , m' , b')) | .(just (a' , n' , c')) with rec n' n'<n c'
              ... | rec-eq
                with a' | put l (get (proj₁ bxalg₁-data) nothing) (n' , c')
              step n rec c | refl | m , b | inj₂ (a , m' , b' , refl , m'<m) | inj₂ (a' , n' , c' , refl , n'<n)
                           | .(just (a , m' , b')) | .(just (a' , n' , c')) | rec-eq | .a | .(m' , b')
                with terminating₁ {b = b'} | terminating₂ {c = c'}
              step n rec c | refl | m , b | inj₂ (a , m' , b' , refl , m'<m) | inj₂ (a' , n' , c' , refl , n'<n)
                           | .(just (a , m' , b')) | .(just (a' , n' , c')) | rec-eq | .a | .(m' , b')
                           | inj₁ eq-nothing₁ | inj₁ eq-nothing₂
                = refl
              step n rec c | refl | m , b | inj₂ (a , m' , b' , refl , m'<m) | inj₂ (a' , n' , c' , refl , n'<n)
                           | .(just (a , m' , b')) | .(just (a' , n' , c')) | rec-eq | .a | .(m' , b')
                           | inj₂ (_ , m'' , b'' , eq-just₁ , m''<m') | inj₂ (_ , n'' , c'' , eq-just₂ , n''<n')
                with <′-wellFounded′ m m' m'<m | <′-wellFounded′ n n' n'<n
              ... | acc rs₁ | acc rs₂
                rewrite Acc-<′-unique m'' (rs₁ m'' m''<m') (<′-wellFounded′ m' m'' m''<m')
                      | Acc-<′-unique n'' (rs₂ n'' n''<n') (<′-wellFounded′ n' n'' n''<n')
                = cong₂ _∷_ refl rec-eq
      put-fusion : ∀ {as : List S} {n} {c : T n} →
                   p₁ as (put l (g₁ as) (n , c)) ≡ p₂ as (n , c)
      put-fusion {[]} {n} {c} = put-fusion-nil n c
      put-fusion {a ∷ as} {n} {c}
        with put-fuse {just (a , g₁ as)} {n , c}
                      (transport′ (cong (λ pred → pred (get l (get bxalg₁ (just (a , g₁ as)))) (n , c))
                                        (sym (proj₂ l-conds))) tt)
      ... | pf with g₂ as            | get-fusion {as}
      ...         | .(get l (g₁ as)) | refl
        with put bxalg₂ (just (a , get l (g₁ as))) (n , c)
           | put bxalg₁ (just (a , g₁ as)) (put l (get bxalg₁ (just (a , g₁ as))) (n , c))
      put-fusion {a ∷ as} {n} {c}
        | refl | .(get l (g₁ as)) | refl | just (a' , n' , c') | just (.a' , .(put l (g₁ as) (n' , c')))
        = cong₂ _∷_ refl (put-fusion {as} {n'} {c'})
      put-fusion {a ∷ as} {n} {c} | refl | .(get l (g₁ as)) | refl | nothing | nothing = refl
