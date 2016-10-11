module HeterogenuousVec where

open import Data.List
open import Relation.Binary
open import Level
open import Data.Fin
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (map)

-- Types

data HVec {l} {I : Set} (A : I -> Set l) : List I → Set l where
  ⟨⟩  : HVec A []
  _▹_ : ∀ {i} {is} → (v : A i) → (vs : HVec A is) → HVec A (i ∷ is)

infixr 6 _▹_
infixr 5 _∈_

data _∈_ {l} {I} {A : I → Set l} : {i : I} {is : List I} → A i →
         HVec A is → Set l where
  here  : ∀ {i} {is} {v : A i} {vs : HVec A is} → v ∈ v ▹ vs
  there : ∀ {i i'} {is} {v : A i} {w : A i'} {vs : HVec A is}
                   (v∈vs : v ∈ vs) → v ∈ w ▹ vs


-- Operations

{-
List indexing.
-}
_‼_ : ∀ {l} {A : Set l} (xs : List A) → Fin (length xs) → A
[] ‼ ()
(x ∷ _) ‼ zero     = x
(_ ∷ xs) ‼ (suc n) = xs ‼ n

{-
HVec indexing
-}
_‼v_ : ∀ {l I} {is : List I} {A : I → Set l} →
         (vs : HVec A is) → (n : Fin (length is)) → A (is ‼ n)
⟨⟩ ‼v ()
(v ▹ _) ‼v zero = v
(_ ▹ vs) ‼v suc n = vs ‼v n

{-
Map
-}
mapHVec : ∀ {l₀ l₁ I} {A : I → Set l₀} {A' : I → Set l₁} {is : List I} →
         (f : (i : I) → (A i) → (A' i)) → (vs : HVec A is) → HVec A' is
mapHVec {is = []} f ⟨⟩ = ⟨⟩
mapHVec {is = i₀ ∷ is} f (v₀ ▹ vs) = f i₀ v₀ ▹ mapHVec f vs


{-
Extension of predicates
-}
data _⇨v_ {l₀ l₁ I} {A : I → Set l₀} (P : (i : I) → A i → Set l₁) :
           {is : List I} → HVec A is → Set (l₀ ⊔ l₁) where
     ⇨v⟨⟩ : P ⇨v ⟨⟩
     ⇨v▹ : ∀ {i} {is} {v} {vs} → (pv : P i v) →
             _⇨v_ P {is} vs → P ⇨v (_▹_ {i = i} v vs)


⇨v-pointwise : ∀ {l₀ l₁ I} {is : List I} {A : I → Set l₀}
                 {P : (i : I) → A i → Set l₁} →
                 (vs : HVec A is) → P ⇨v vs →
                 (n : Fin (length is)) → P (is ‼ n) (vs ‼v n)
⇨v-pointwise {is = []} ⟨⟩ p ()
⇨v-pointwise {is = i ∷ is} (v ▹ vs) (⇨v▹ pv pvs) zero = pv
⇨v-pointwise {is = i ∷ is} (v ▹ vs) (⇨v▹ pv pvs) (suc n) = ⇨v-pointwise vs pvs n


{-
Extension of relations
-}
data _∼v_ {l₀ l₁ I} {A : I → Set l₀} {R : (i : I) → Rel (A i) l₁} :
          {is : List I} → Rel (HVec A is) (l₀ ⊔ l₁) where
     ∼⟨⟩ : ⟨⟩ ∼v ⟨⟩
     ∼▹  : ∀ {i} {is} {t₁} {t₂} {ts₁ : HVec A is} {ts₂ : HVec A is} →
           R i t₁ t₂ → _∼v_ {R = R} ts₁ ts₂ → (t₁ ▹ ts₁) ∼v (t₂ ▹ ts₂)


~v-pointwise : ∀ {l₀} {l₁} {I : Set} {is : List I}
               {A : I → Set l₀} {R : (i : I) → Rel (A i) l₁} →
               (vs₁ vs₂ : HVec A is) → _∼v_ {R = R} vs₁ vs₂ →
               (n : Fin (length is)) → R (is ‼ n) (vs₁ ‼v n) (vs₂ ‼v n)
~v-pointwise ⟨⟩ .⟨⟩ ∼⟨⟩ ()
~v-pointwise (v₁ ▹ vs₁) (v₂ ▹ vs₂) (∼▹ v₁∼v₂ eq) zero = v₁∼v₂
~v-pointwise (v₁ ▹ vs₁) (v₂ ▹ vs₂) (∼▹ v₁∼v₂ eq) (suc n) =
                                                 ~v-pointwise vs₁ vs₂ eq n


-- Reindexing


reindex : ∀ {l} {I I' : Set}
              (fᵢ : I → I') → {A : I' → Set l} → {is : List I} →
              HVec (A ∘ fᵢ) is → HVec A (map fᵢ is)
reindex fᵢ ⟨⟩ = ⟨⟩
reindex fᵢ (v ▹ vs) = v ▹ reindex fᵢ vs


{-
Reindex of extension of predicates
-}
⇨v-reindex : ∀ {l₀ l₁ I I'} {is : List I}
             {A : I' → Set l₀} {P : (i : I') → A i → Set l₁} →
             (fᵢ : I → I') → {vs : HVec (A ∘ fᵢ) is} →
             (P ∘ fᵢ) ⇨v vs → P ⇨v (reindex fᵢ vs)
⇨v-reindex fᵢ ⇨v⟨⟩ = ⇨v⟨⟩
⇨v-reindex fᵢ (⇨v▹ pv p) = ⇨v▹ pv (⇨v-reindex fᵢ p)


{-
Reindex of extension of relations
-}
∼v-reindex : ∀ {l₀} {l₁} {I I' : Set} {is : List I}
             {A : I' → Set l₀} {R : (i : I') → Rel (A i) l₁} →
             (fᵢ : I → I') → {vs₁ vs₂ : HVec (A ∘ fᵢ) is} →
             _∼v_ {R = R ∘ fᵢ} vs₁ vs₂ →
             _∼v_ {I = I'} {R = R}
                  (reindex fᵢ vs₁)
                  (reindex fᵢ vs₂)
∼v-reindex fₛ ∼⟨⟩ = ∼⟨⟩
∼v-reindex fᵢ (∼▹ v₁∼v₂ eq) = ∼▹ v₁∼v₂ (∼v-reindex fᵢ eq)


{-
Mapping reindexed vectors
-}
mapReindex : ∀ {l₀ l₁ I I' is} {A₀ : I' → Set l₀} {A₁ : I' → Set l₁} →
              (fᵢ : I → I') → (h : (i : I') → A₀ i → A₁ i) →
              (vs : HVec (A₀ ∘ fᵢ) is) →
              mapHVec h (reindex fᵢ vs) ≡ reindex fᵢ (mapHVec (h ∘ fᵢ) vs)
mapReindex {is = []} fᵢ h ⟨⟩ = refl
mapReindex {is = i₀ ∷ is} fᵢ h (v ▹ vs) = cong (λ vs' → h (fᵢ i₀) v ▹ vs')
                                               (mapReindex fᵢ h vs)


-- Other properties

{-
Map y composición
-}
propMapV∘ : ∀ {l₀ l₁ l₂ I is}  {A₀ : I → Set l₀} {A₁ : I → Set l₁}
              {A₂ : I → Set l₂} → (vs : HVec A₀ is) →
              (m : (i : I) → (A₀ i) → (A₁ i)) →
              (m' : (i : I) → (A₁ i) → (A₂ i)) →
              mapHVec m' (mapHVec m vs)
              ≡
              mapHVec (λ s' → m' s' ∘ m s') vs
propMapV∘ {is = []} ⟨⟩ m m' = refl
propMapV∘ {is = i₀ ∷ is} (v₀ ▹ vs) m m' = cong₂ (λ x y → x ▹ y) refl
                                                (propMapV∘ vs m m')


-- HVec Setoid


open Setoid

HVecSet : ∀ {l₁ l₂} → (I : Set) → (A : I → Setoid l₁ l₂) →
                       List I → Setoid _ _
HVecSet I A is = record { Carrier = HVec (λ i → Carrier $ A i) is
                       ; _≈_ = _∼v_ {R = λ i → _≈_ (A i)}
                       ; isEquivalence = record { refl = refl~v is
                                                ; sym = sym~v is
                                                ; trans = trans~v is }
                       }

  where refl~v : (is' : List I) → Reflexive (_∼v_ {R = λ i → _≈_ (A i)}
                                                  {is = is'})
        refl~v .[] {⟨⟩} = ∼⟨⟩
        refl~v (i ∷ is') {v ▹ vs} = ∼▹ (Setoid.refl (A i)) (refl~v is')

        sym~v : (is' : List I) → Symmetric (_∼v_ {R = λ i → _≈_ (A i)}
                                                 {is = is'})
        sym~v .[] {⟨⟩} ∼⟨⟩ = ∼⟨⟩
        sym~v (i ∷ is) {v ▹ vs} (∼▹ v≈w vs≈ws) = ∼▹ (Setoid.sym (A i) v≈w)
                                                    (sym~v is vs≈ws)

        trans~v : (is' : List I) → Transitive (_∼v_ {R = λ i → _≈_ (A i)}
                                                    {is = is'})
        trans~v .[] {⟨⟩} ∼⟨⟩ ∼⟨⟩ = ∼⟨⟩
        trans~v (i ∷ is₁) {v ▹ vs} (∼▹ v≈w vs≈ws)
                                   (∼▹ w≈z ws≈zs) = ∼▹ (Setoid.trans (A i) v≈w w≈z)
                                                       (trans~v is₁ vs≈ws ws≈zs)
