module UniCombinatorsAndProperties where

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
open import Data.IntegerOmega.Base as ℤω
open import Data.IntegerOmega.Properties
import Data.Integer as ℤ
open import Induction.WellFounded
open import Data.Nat.Induction
open import Data.Bool
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality



b≢true⇒b≡false : ∀ (b : Bool) → (b ≡ true → ⊥) → b ≡ false
b≢true⇒b≡false false neq = refl
b≢true⇒b≡false true neq = ⊥-elim (neq refl)



map-fusion : ∀ {A B C : Set} →
               {xs : List A} →
               (f : A → B) → (g : B → C) →
               ((map g) ∘ (map f)) xs ≡ map (g ∘ f) xs
map-fusion {A} {B} {C} {[]} f g = refl
map-fusion {A} {B} {C} {x ∷ xs} f g = cong₂ _∷_ refl (map-fusion f g)



-- non-standard scanl
scanl : ∀ {A B : Set} → (A → B → A) → A → List B → List A
scanl f e [] = []
scanl f e (x ∷ xs) = f e x ∷ scanl f (f e x) xs
  
inits : ∀ {A : Set} → List A → List (List A)
inits = scanl (λ x y → x ++ (y ∷ [])) []
  
length-inits : ∀ {A : Set} →
               ∀ (xs₀ : List A) →
               ∀ (xs : List A) →
               length xs ≡ length (scanl (λ x₁ y → x₁ ++ y ∷ []) xs₀ xs)
length-inits xs₀ [] = refl
length-inits xs₀ (x ∷ xs) = cong suc (length-inits (xs₀ ++ x ∷ []) xs)
    
inits-acc : ∀ {A : Set} →
            ∀ {xs₀ : List A} {xs : List A} →
            scanl (λ (x : List A) (y : A) → x ++ y ∷ []) xs₀ xs ≡ map (_++_ xs₀) (scanl (λ x y → x ++ y ∷ []) [] xs)
inits-acc {A} {xs₀} {[]} = refl
inits-acc {A} {xs₀} {x ∷ xs} rewrite inits-acc {A} {x ∷ []} {xs}
  = cong₂ _∷_ refl
              (begin
                 scanl (λ z z₁ → z ++ z₁ ∷ []) (xs₀ ++ x ∷ []) xs
               ≡⟨ inits-acc {A} {xs₀ ++ x ∷ []} {xs} ⟩
                 map (_++_ (xs₀ ++ x ∷ [])) (scanl (λ x₁ y → x₁ ++ y ∷ []) [] xs)
               ≡⟨ cong (λ f → map f (scanl (λ x₁ y → x₁ ++ y ∷ []) [] xs))
                       (funext (λ xs → Data.List.Properties.++-assoc xs₀ (x ∷ []) xs))  ⟩
                 map (λ z → xs₀ ++ x ∷ z) (scanl (λ z z₁ → z ++ z₁ ∷ []) [] xs)
               ≡⟨ sym (map-fusion {xs = scanl (λ x₁ y → x₁ ++ y ∷ []) [] xs} (List._∷_ x) (_++_ xs₀)) ⟩
                 map (_++_ xs₀) (map (_∷_ x) (scanl (λ z z₁ → z ++ z₁ ∷ []) [] xs))
               ∎)
  
inits-injective : ∀ {A : Set} →
                  ∀ (xs₁ xs₂ : List A) →
                  inits xs₁ ≡ inits xs₂ → xs₁ ≡ xs₂
inits-injective {A} xs₁ xs₂ eq = inits-injective-aux [] xs₁ xs₂ eq
    where inits-injective-aux : ∀ (xs₀ xs₁ xs₂ : List A) →
                                scanl (λ x y → x ++ y ∷ []) xs₀ xs₁ ≡ scanl (λ x y → x ++ y ∷ []) xs₀ xs₂ →
                                xs₁ ≡ xs₂
          inits-injective-aux xs₀ [] [] eq = refl
          inits-injective-aux xs₀ (x₁ ∷ xs₁) (x₂ ∷ xs₂) eq with Data.List.Properties.∷-injective eq
          ... | eq₁ , eq₂ with Data.List.Properties.++-cancelˡ xs₀ {x₁ ∷ []} {x₂ ∷ []} eq₁
          inits-injective-aux xs₀ (x₁ ∷ xs₁) (.x₁ ∷ xs₂) eq | eq₁ , eq₂ | refl
            = cong₂ _∷_ refl (inits-injective-aux (xs₀ ++ x₁ ∷ []) xs₁ xs₂ eq₂)


_ : inits (1 ∷ 2 ∷ []) ≡ ((1 ∷ []) ∷ (1 ∷ 2 ∷ []) ∷ [])
_ = refl


init : ∀ {A : Set} → List A → List A
init [] = []
init (a ∷ []) = []
init (a ∷ b ∷ as) = a ∷ init (b ∷ as)
  
_ : init (1 ∷ 2 ∷ 3 ∷ []) ≡ 1 ∷ 2 ∷ []
_ = refl
  
  
[]≠snoc : ∀ {A : Set} → ∀ (xs : List A) x →
          ∃[ x′ ] (∃[ xs′ ] (xs ++ x ∷ [] ≡ x′ ∷ xs′))
[]≠snoc [] x = x , [] , refl
[]≠snoc (x₁ ∷ xs) x = x₁ , xs ++ x ∷ [] , refl
  
-- non-standard scanr
scanr : ∀ {A B : Set} → (A → B → B) → B → List A → List B
scanr f e [] = []
scanr f e (a ∷ as) with scanr f e as
... | [] = f a e ∷ []
... | b ∷ bs = f a b ∷ b ∷ bs
  


tails : ∀ {A : Set} → List A → List (List A)
tails = scanr _∷_ []
  
tails-nil : ∀ {A : Set} →
              scanr (λ (x : A) (y : List A) → x ∷ y)  [] [] ≡ []
tails-nil = refl

  
tails-cons : ∀ {A : Set} →
             ∀ (x : A) (xs : List A) →
             tails (x ∷ xs) ≡ (x ∷ xs) ∷ tails xs
tails-cons x [] = refl
tails-cons x (x₁ ∷ xs) with tails-cons x₁ xs
... | eq with tails xs
tails-cons x (x₁ ∷ .[]) | refl | [] = refl
tails-cons x (x₁ ∷ xs) | refl | .xs ∷ xss = refl
  
tails-unique : ∀ {A : Set} →
               ∀ (xs : List A) (xss : List (List A)) (xs′ : List A) →
               xs ∷ xss ≡ tails xs′ →
               xs ≡ xs′
tails-unique xs xss (x ∷ xs′) eq rewrite tails-cons x xs′ = Data.List.Properties.∷-injectiveˡ eq
  
tails-snoc : ∀ {A : Set} →
             ∀ (xs : List A) x →
             tails (xs ++ x ∷ []) ≡ map (λ xs → xs ++ x ∷ []) (tails xs) ++ (x ∷ []) ∷ []
tails-snoc [] x = refl
tails-snoc (x₁ ∷ xs) x with tails-snoc xs x |  tails-cons x₁ xs
... | eq | eq₁  with tails (xs ++ x ∷ [])
tails-snoc (x₁ ∷ xs) x | eq | eq₁ | [] with []≠snoc (map (λ xs₁ → xs₁ ++ x ∷ []) (scanr _∷_ [] xs)) (x ∷ []) -- failed branch
... | x′ , xs′ , eq′ with trans eq eq′
... | () 
tails-snoc (x₁ ∷ xs) x | eq | eq₁ | xs′ ∷ xss with tails xs
tails-snoc (x₁ ∷ .[]) x | refl | refl | .(x ∷ []) ∷ .[] | [] = refl
tails-snoc (x₁ ∷ .xs′′) x
  | refl | refl | .(xs′′ ++ x ∷ []) ∷ .(map (λ xs → xs ++ x ∷ []) xss′ ++ (x ∷ []) ∷ []) | xs′′ ∷ xss′ = refl
  
  
tails-injective : ∀ {A : Set} →
                  ∀ (xs₁ xs₂ : List A) →
                  tails xs₁ ≡ tails xs₂ →
                  xs₁ ≡ xs₂
tails-injective [] [] eq = refl
tails-injective [] (x ∷ xs₂) eq with trans eq (tails-cons x xs₂)
... | ()
tails-injective (x ∷ xs₁) [] eq with trans (sym eq) (tails-cons x xs₁)
... | ()
tails-injective (x ∷ xs₁) (x₁ ∷ xs₂) eq with tails-cons x xs₁ | tails-cons x₁ xs₂
... | eq₁ | eq₂ with Data.List.Properties.∷-injective (trans (trans (sym eq₁) eq) eq₂)
... | eq₃ , eq₄ = eq₃
  
head : ∀ {A : Set} → List A → Maybe A
head [] = nothing
head (x ∷ _) = just x
  
  
last : ∀ {A : Set} → A → List A → A
last a [] = a
last a (x ∷ as) = last x  as

map-last : ∀ {A B : Set} →
           ∀ {a} {as} →
           (f : A → B) →
           last (f a) (map f as) ≡ f (last a as)
map-last {a = a} {[]} f = refl
map-last {a = a} {a₁ ∷ as} f = map-last {a = a₁} {as = as} f

last-computation : ∀ {A : Set} {x : A} {xs : List A} {x′ : A} →
                   last x (xs ++ x′ ∷ []) ≡ x′
last-computation {_} {x} {[]} {x′} = refl
last-computation {A} {x} {x₁ ∷ xs} {x′} = last-computation {A} {x₁} {xs} {x′}
  
last-snoc : ∀ {A : Set} {x : A} {xs xs′ : List A} {x′ : A} →
            xs′ ++ x′ ∷ [] ≡ x ∷ xs →
            last x xs ≡ x′
last-snoc {A} {x} {[]} {[]} {.x} refl = refl
last-snoc {A} {x} {[]} {x₁ ∷ xs′} {x′} eq with Data.List.Properties.∷-injectiveʳ eq
... | eq₁ with []≠snoc xs′ x′
... | _ , _ , eq₂ with trans (sym eq₁) eq₂
... | ()
last-snoc {A} {x} {x₁ ∷ xs} {x₂ ∷ xs′} {x′} eq
  = last-snoc {A} {x₁} {xs} {xs′} {x′} (Data.List.Properties.∷-injectiveʳ eq)


reverseAcc-snoc≡cons : ∀ {A : Set} →
                       ∀ (xs₀ xs : List A) (x : A) →
                       foldl (λ x y → y ∷ x) xs₀ (xs ++ x ∷ []) ≡ x ∷ foldl (λ x y → y ∷ x) xs₀ xs
reverseAcc-snoc≡cons xs₀ [] x = refl
reverseAcc-snoc≡cons xs₀ (x₁ ∷ xs) x = reverseAcc-snoc≡cons (x₁ ∷ xs₀) xs x
  
reverse-snoc≡cons : ∀ {A : Set} →
                    ∀ (xs : List A) (x : A) →
                    reverse (xs ++ x ∷ []) ≡ x ∷ reverse xs
reverse-snoc≡cons = reverseAcc-snoc≡cons []


reverse-cons≡snoc : ∀ {A : Set} →
                    ∀ (x : A) (xs : List A) →
                    reverse (x ∷ xs) ≡ reverse xs ++ x ∷ []
reverse-cons≡snoc x xs = Data.List.Properties.reverse-++-commute (x ∷ []) xs
  
reverse-acc : ∀ {A : Set} →
              ∀ (xs₀ xs : List A) →
              foldl (λ x y → y ∷ x) xs₀ xs ≡ reverse xs ++ xs₀
reverse-acc xs₀ [] = refl
reverse-acc xs₀ (x ∷ xs) = begin
                               foldl (λ x y → y ∷ x) (x ∷ xs₀) xs
                             ≡⟨ reverse-acc (x ∷ xs₀) xs ⟩
                               reverse xs ++ x ∷ xs₀
                             ≡⟨ sym (Data.List.Properties.++-assoc (reverse xs) (x ∷ []) xs₀) ⟩
                               (reverse xs ++ x ∷ []) ++ xs₀
                             ≡⟨ sym (cong (λ xs → xs ++ xs₀) (reverse-cons≡snoc x xs)) ⟩
                               reverse (x ∷ xs) ++ xs₀
                             ∎


sum : List ℤω → ℤω
sum = foldr ℤω._+_ (fin ℤ.+0)
 
sum-++-commute : ∀ xs ys → sum (xs ++ ys) ≡ sum xs ℤω.+ sum ys
sum-++-commute [] ys = sym (Data.IntegerOmega.Properties.+-identityˡ (sum ys))
sum-++-commute (x ∷ xs) ys
  rewrite sum-++-commute xs ys = sym (+-assoc x (foldr ℤω._+_ (fin (ℤ.+ 0)) xs) (foldr ℤω._+_ (fin (ℤ.+ 0)) ys))
  

z⊓-∞≡-∞ : ∀ z → z ℤω.⊓ -∞ ≡ -∞
z⊓-∞≡-∞ z = Data.IntegerOmega.Properties.i≥j⇒i⊓j≡j -∞≤any


maximum : List ℤω → ℤω
maximum = foldr ℤω._⊔_ -∞

  
maximum-singleton : ∀ z → maximum (z ∷ []) ≡ z
maximum-singleton z rewrite ⊔-identityʳ z = refl
  
maximum-snoc : ∀ {xs} {x} →
               maximum (xs ++ x ∷ []) ≡ maximum xs ℤω.⊔ x
maximum-snoc {[]} {x} = Data.IntegerOmega.Properties.⊔-comm x -∞
maximum-snoc {x₁ ∷ xs} {x}
  rewrite maximum-snoc {xs} {x} = sym (Data.IntegerOmega.Properties.⊔-assoc x₁ (maximum xs) x)

maximum-map-snoc-promotion : ∀ {b} {as} →
                             maximum (map (ℤω._+_ b) as ++ b ∷ []) ≡ b ℤω.+ (maximum (as ++ (fin ℤ.+0) ∷ []))
maximum-map-snoc-promotion {b} {[]} rewrite ⊔-identityʳ b | ⊔-identityʳ (fin (ℤ.+0)) = sym (Data.IntegerOmega.Properties.+-identityʳ b)
maximum-map-snoc-promotion {b} {a ∷ as} = begin
                                              b ℤω.+ a ℤω.⊔ maximum (map (ℤω._+_ b) as ++ b ∷ [])
                                            ≡⟨ cong (λ c → b ℤω.+ a ℤω.⊔ c) (maximum-map-snoc-promotion {b} {as}) ⟩
                                              b ℤω.+ a ℤω.⊔ (b ℤω.+ maximum (as ++ (fin ℤ.+0) ∷ []))
                                            ≡⟨ sym (+-distribˡ-⊔ b a (maximum (as ++ (fin ℤ.+0) ∷ []))) ⟩
                                              b ℤω.+ (a ℤω.⊔ maximum (as ++ (fin ℤ.+0) ∷ []))
                                            ∎

maximum≢-∞-lemma : ∀ xs → maximum (xs ++ +0 ∷ []) ≡ -∞ → ⊥
maximum≢-∞-lemma xs eq with maximum (xs ++ +0 ∷ []) |  maximum-snoc {xs = xs} {x = +0}
... | .(maximum xs ℤω.⊔ +0) | refl with maximum xs
maximum≢-∞-lemma xs () | .(foldr ℤω._⊔_ -∞ xs ℤω.⊔ fin (ℤ.+ _)) | refl | -∞
maximum≢-∞-lemma xs () | .(foldr ℤω._⊔_ -∞ xs ℤω.⊔ fin (ℤ.+ _)) | refl | fin x

maximum-map-snoc-promotion′ : ∀ {b} {as} → maximum (map (ℤω._+_ b) as ++ b ∷ []) - (maximum (as ++ +0 ∷ [])) ≡ b
maximum-map-snoc-promotion′ {b} {as}
    = begin
        maximum (map (ℤω._+_ b) as ++ b ∷ []) - (maximum (as ++ +0 ∷ []))
      ≡⟨ cong (λ a → a - (maximum (as ++ +0 ∷ []))) (maximum-map-snoc-promotion {b} {as}) ⟩
        b ℤω.+ maximum (as ++ +0 ∷ []) - maximum (as ++ +0 ∷ [])
      ≡⟨  Data.IntegerOmega.Properties.+-assoc b (maximum (as ++ +0 ∷ [])) (- maximum (as ++ +0 ∷ [])) ⟩
        b ℤω.+ (maximum (as ++ +0 ∷ []) - maximum (as ++ +0 ∷ []))
      ≡⟨ cong (ℤω._+_ b) (i≡j∧j≢-∞⇒i-j≡0 (maximum (as ++ +0 ∷ [])) (maximum (as ++ +0 ∷ [])) refl (maximum≢-∞-lemma as)) ⟩
        b ℤω.+ +0
      ≡⟨ Data.IntegerOmega.Properties.+-identityʳ b ⟩
        b
      ∎


  
∷-++-assoc : ∀ {A : Set} →
               (x : A) (xs : List A) (ys : List A) →
               (x ∷ xs) ++ ys ≡ x ∷ (xs ++ ys)
∷-++-assoc x xs ys = refl

init-snoc : ∀ {A : Set} →
            (xs : List A) (x : A) →
            init (xs ++ (x ∷ [])) ≡ xs
init-snoc [] x = refl
init-snoc (y ∷ []) x = refl
init-snoc (y ∷ z ∷ xs) x = cong₂ _∷_ refl (init-snoc (z ∷ xs) x)

tails-list-unique : ∀ {A : Set} →
                    (a b : ∃[ xss ] (∃[ xs ] (tails {A} xs ≡ xss))) →
                    (proj₁ a ≡ proj₁ b) →
                    a ≡ b
tails-list-unique (.(scanr _∷_ [] xs) , xs , refl) (.(scanr _∷_ [] xs) , xs′ , eq₂) refl with tails-injective xs′ xs eq₂
tails-list-unique (.(tails xs) , xs , refl) (.(tails xs) , .xs , refl) refl | refl = refl
