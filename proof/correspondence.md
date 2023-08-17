# Correspondence between proofs and paper descriptions

We formally verified the proposed contract lenses, combinators and calculation theorems. In this documentation, we provide pointers that indicate where the proofs for each definition in the paper can be found.

## Section 4
- __Definition 1__: In `Lens.agda`, line 20-33
- __Definition 2__ and __Theorem 1__: In `Lens.agda`, line 38-66. The `general-compose` theorem describes the composition condition. Well-behavedness is entailed directly by the result type `Lens S T`. Also, we provide syntactic abbreviation `_;_[_,_]`. An expression `l1 ; l2 [ proof1 , proof2 ]` represents a composition between `l1` and `l2`. The additional proofs `proof1`, `proof2` are the composition conditions required in Definition 2.
- __Definition 3__ and __Theorem 2__: In `Lens.agda`, line 120-168

## Section 5
The main proofs for our combinators and theorems are in `Core.agda`. We also list theorem statements separately in `Combinators.agda` and `Theorems.agda`.

- __bfoldr__: In `Combinators.agda`, line 22-25, the combinator is presented as `bfold`. We use a syntactic abbreviation `l hasConditions P and Q` to express the fact that lens `l` has source contract `P` and view contract `Q`. You can find the actual proof in `Core.agda`, line 2138-2183. Due to the fact that the usual `unfold` does not guarantee termination, we added the `{-# TERMINATING #-}` pragma. In `TerminatingFold.agda`, you can find a proof for the correctness of `bfoldr` and `bfoldr-fusion-law` when a terminating condition is imposed on `unfold`.

- __bfoldr'__: In `Combinators.agda`, line 29-36, the combinator is presented as `bfold'`. You can find the actual proof in `Core.agda`, line 2052-2086. Note that we put some commonly used conditions in a separate module `CommonConditions`, which can be found in `Core.agda`, starting from line 85. For example, the `CommonConditions.lift` conditions can be found in `Core.agda`, line 138.
The proof of this combinator can be found in `Core.agda`, line 2052-2086.

- __bfilter__ and __bfilterAlg__: In `Core.agda`, line 2090-2135. In `bfilter`, line 2135, you can find that `bfilter` is defined as a __bfoldr__.


- __bmap__: In `Combinators.agda`, line 40-43, the combinator is presented as `bmap`. You can find the actual proof in `Core.agda`, line 2293-2324.

- __bmap'__: In `Core.agda`, line 2326-2349, the combinator is proved as `bxmap2`.

- __bmapl__: In `Combinators.agda`, line 46-54, the combinator is presented as `bmapl-paper`. Here the syntactic sugar mentioned in the paper is encoded by the following dependent type:
```agda
(ℓ-data : (a : S) → (Σ (Lens S V) λ ℓ → ℓ hasConditions (λ _ a′ → P a a′)
                                         and            λ _ b′ → Q (get ℓ a) b′)) →
         (Σ (S → V) λ f → ∀ (a a′ : S) → get (proj₁ (ℓ-data a)) a′ ≡ f a′) → ...
```

As mentioned in Section 9, our agda proof works primarily with another version of this combinator, which can be found in `Combinators.agda`, line 57-66, `bmapl-comb`. The main difference is the type of components: `S => (S <-> V)` and `(S * S) <-> (V * V)`. These two components are actually equivalent. We prove this by providing two conversion functions, informally
```agda
bmapl-component : (S => (S <-> V)) -> ((S * S) <-> (V * V))
bmapl-component-reverse : ((S * S) <-> (V * V)) -> (S => (S <-> V))
```
and prove that `bmapl-component` is the inverse of `bmapl-component-reverse`. The proof can be found in `Core.agda`, line 265-349.

In later examples, we use `bmapl-comb` instead of `bmapl-paper`.

The actual proof of `bmapl-paper` and `bmapl-comb` can be found in `Core.agda`, line 457-467, line 352-452, respectively. Note that `bmap'` is defined in terms of `bmapl-comb`, by using the above conversion functions.


- __bfoldl_init__: In `Combinator.agda`, line 70-77, the combinator is presented as `bfoldlᵢₙᵢₜ-paper`. Similarly as __bmapl__, we work with a slightly different version `bfold-inits` (line 80-90, `Combinator.agda`). The proof can be found in `Core.agda`, line 1522-1530 and line 1387-1519.

`bfoldlᵢₙᵢₜ-component-source-condition` can be found in `Core.agda`, line 1346.

- __bscanl__: In `Combinator.agda`, line 95-102, the combinator is presented as `bscanl-paper`. Similarly, we work with a slightly different version `bscanl-comb` (line 105-115, `Combinator.agda`). The proof can be found in `Core.agda`, line 1534-1542 and line 1222-1304.


## Section 6
- __bfoldr-fusion__ and __bfoldr'-fusion__: In `Theorems.agda`, line 31-71. The types look lengthy, but codes inside brackets are simply proofs for convincing Agda that lens compositions are valid. It is more readable if things inside brackets are ignored. For example, informally, `bfold'-fusion` read:
```agda
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
                 ((proj₁ bxalg₁-data ； proj₁ l-data) ≈ blistf′ cs cv ct l-data ； proj₁ bxalg₂-data) 
                 →
                 bxfold-conditioned cs cv bxalg₁-data ； proj₁ l-data ≈ bxfold-conditioned cs ct bxalg₂-data
```

The proof of these two laws can be found in `Core.agda`, line 2635-2707, line 2585-2631. A version with termination condition can be found in `TerminatingFold.agda`, line 146.

- __;; composition__ We define the special lens composition operator `_;;_` in `Core.agda`, line 470-500. 

Since we work primarily with another version of __bmapl__ which takes component of type `(S * S) <-> (V * V)`, we prove a theorem that says our conversion function `bmapl-component` is acually a homomorphism:
```agda
bmapl-component (l1 ;; l2) ≈ bmapl-component l1 ; bmapl-component l2
```
The proof can be found in `Core.agda`, line 505-533.

- __bmapl-fusion__: The statement of the theorem can be found in `Theorems.agda`, line 76-113. The proof can be found in `Core.agda`, line 609-798.

- __bfoldr'-map-fusion__: The statement of the theorem can be found in `Theorem.agda`, line 120-132. The proof can be found in `Core.agda`, line 2476-2513.

- __bscanl-lemma__: The statement can be found in `Theorem.agda`, line 136-154. The proof can be found in `Core.agda`, line 1875-2023.


## Overview and Section 7
The example lenses and calculation steps are provided in `Examples.agda`.

