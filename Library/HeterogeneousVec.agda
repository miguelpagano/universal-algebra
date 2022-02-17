------------------------------------------------------------
-- Universal Algebra Library
--
-- Heterogeneous vectors
------------------------------------------------------------
module HeterogeneousVec where
open import Data.Fin
open import Data.List renaming (map to lmap;lookup to _‼_)
  hiding (zip;zipWith)
open import Data.Product hiding (map;zip)
open import Data.Unit hiding (setoid)
open import Function hiding (_⟶_)
open import Function.Equality as FE hiding (cong;_∘_;id)
open import Level
open import Relation.Binary
open import Relation.Binary.Indexed.Homogeneous
  hiding (Rel;Reflexive;Symmetric;Transitive)
import Relation.Binary.PropositionalEquality as PE
open import Relation.Unary using (Pred)
open import Relation.Unary.Indexed using (IPred)

-- Types

data HVec {l} {I : Set} (A : I -> Set l) : List I → Set l where
  ⟨⟩  : HVec A []
  _▹_ : ∀ {i is} → (v : A i) → (vs : HVec A is) → HVec A (i ∷ is)

infixr 6 _▹_
infixr 5 _∈_

pattern ⟨⟨_,_⟩⟩ a b = a ▹ (b ▹ ⟨⟩)
pattern ⟪_⟫ a = a ▹ ⟨⟩

data _∈_ {l} {I} {A : I → Set l} : {i : I} {is : List I} → A i →
         HVec A is → Set l where
  here  : ∀ {i} {is} {v : A i} {vs : HVec A is} → v ∈ v ▹ vs
  there : ∀ {i i'} {is} {v : A i} {w : A i'} {vs : HVec A is}
            (v∈vs : v ∈ vs) → v ∈ w ▹ vs


-- Operations

{- HVec indexing -}
_‼v_ : ∀ {l I} {is : List I} {A : I → Set l} →
       (vs : HVec A is) → (n : Fin (length is)) → A (is ‼ n)
(v ▹ _) ‼v zero = v
(_ ▹ vs) ‼v suc n = vs ‼v n

_++v_ : ∀ {l I} {is is' : List I} {A : I → Set l} →
         (vs : HVec A is) → (vs' : HVec A is') → HVec A (is ++ is')
⟨⟩ ++v vs' = vs'
(v ▹ vs) ++v vs' = v ▹ (vs ++v vs')

zip : ∀ {l₀ l₁ I} {A : I → Set l₀} {B : I → Set l₁}  {is : List I} →
      (vs : HVec A is) → (vs' : HVec B is) → HVec (λ i → A i × B i) is
zip ⟨⟩ ⟨⟩ = ⟨⟩
zip (v ▹ vs) (v' ▹ vs') = (v , v') ▹ zip vs vs'

zipWith : ∀ {l₀ l₁ l₂ I} {A : I → Set l₀} {B : I → Set l₁} {C : I → Set l₂} →
          (f : {i : I} → A i → B i → C i) →
          {is : List I} →
          (vs : HVec A is) → (vs' : HVec B is) → HVec C is
zipWith _ ⟨⟩ ⟨⟩ = ⟨⟩
zipWith f (v ▹ vs) (v' ▹ vs') = f v v' ▹ zipWith f vs vs'

map : ∀ {l₀ l₁ I} {A : I → Set l₀} {A' : I → Set l₁} {is : List I} →
      (f : (i : I) → (A i) → (A' i)) → (vs : HVec A is) → HVec A' is
map {is = []} f ⟨⟩ = ⟨⟩
map {is = i₀ ∷ is} f (v₀ ▹ vs) = f i₀ v₀ ▹ map f vs


-- Properties.


-- Extension of predicates
data _⇨v_ {l₀ l₁ I} {A : I → Set l₀} (P : IPred A l₁) :
          {is : List I} → HVec A is → Set (l₀ ⊔ l₁) where
     ⇨v⟨⟩ : P ⇨v ⟨⟩
     ⇨v▹ : ∀ {i is v vs} → (pv : P {i} v) → (pvs : _⇨v_ P {is} vs) → P ⇨v (v ▹ vs)

pattern ⇨⟨⟨_,_⟩⟩∼ a b = ⇨v▹ a (⇨v▹ b ⇨v⟨⟩)

_⇨v : ∀ {l₀ l₁ I} {A : I → Set l₀} (P : IPred A l₁) →
       {is : List I} → Pred (HVec A is) (l₀ ⊔ l₁)
P ⇨v = P ⇨v_

⇨₂ : ∀ {l₀ l₁ I} {A : I → Set l₀} {P : IPred A l₁} →
     {is : List I}
     (as : HVec (λ i → Σ[ a ∈ A i ] (P {i} a)) is) →
     (P ⇨v map (λ _ → proj₁) as)
⇨₂ {P = P} {[]} ⟨⟩ = ⇨v⟨⟩
⇨₂ {P = P} {i ∷ is} ((a , p) ▹ as) = ⇨v▹ p (⇨₂ {P = P} {is} as)

⇨vtoΣ : ∀ {l₀ l₁ I} {A : I → Set l₀} {P : IPred A l₁}
        {is} {vs : HVec A is} → P ⇨v vs →
        HVec (λ i → Σ[ a ∈ A i ] P {i} a) is
⇨vtoΣ ⇨v⟨⟩ = ⟨⟩
⇨vtoΣ (⇨v▹ {v = v} pv p⇨vs) = (v , pv) ▹ ⇨vtoΣ p⇨vs

map⇨v : ∀ {l₀ l₁ l₂ I is} {A : I → Set l₀} {vs : HVec A is}
           {P : IPred A l₁} {P' : IPred A l₂} →
           (f : ∀ {i'} {a : A i'} → P {i'} a → P' {i'} a) →
           P ⇨v vs → P' ⇨v vs
map⇨v f ⇨v⟨⟩ = ⇨v⟨⟩
map⇨v f (⇨v▹ pv pvs) = ⇨v▹ (f pv) (map⇨v f pvs)


proj₁⇨v : ∀ {l₀ l₁ I} {A : I → Set l₀} {P : IPred A l₁}
           {is} {vs : HVec A is} → P ⇨v vs → HVec A is
proj₁⇨v {vs = vs} _ = vs

proj₁-inv-⇨vtoΣ : ∀ {l₀ l₁ I} {A : I → Set l₀} {P : IPred A l₁}
                  {is} {vs : HVec A is} → (ps : P ⇨v vs) →
                  map (λ s → proj₁) (⇨vtoΣ ps) PE.≡ vs
proj₁-inv-⇨vtoΣ {vs = ⟨⟩} ⇨v⟨⟩ = PE.refl
proj₁-inv-⇨vtoΣ {vs = v ▹ vs} (⇨v▹ pv ps) = PE.cong₂ _▹_ PE.refl (proj₁-inv-⇨vtoΣ ps)

⇨v-pointwise : ∀ {l₀ l₁ I} {is : List I} {A : I → Set l₀}
               {P : IPred A l₁} →
               (vs : HVec A is) → P ⇨v vs →
               (n : Fin (length is)) → P {is ‼ n} (vs ‼v n)
⇨v-pointwise {is = []} ⟨⟩ p ()
⇨v-pointwise {is = i ∷ is} (v ▹ vs) (⇨v▹ pv pvs) zero = pv
⇨v-pointwise {is = i ∷ is} (v ▹ vs) (⇨v▹ pv pvs) (suc n) = ⇨v-pointwise vs pvs n


{-
Extension of relations
-}
data _∼v_ {l₀ l₁ I} {A : I → Set l₀} {R : IRel A l₁} :
          {is : List I} → Rel (HVec A is) (l₀ ⊔ l₁) where
     ∼⟨⟩ : ⟨⟩ ∼v ⟨⟩
     ∼▹  : ∀ {i is} {t₁ t₂ : A i} {ts₁ ts₂ : HVec A is} →
           R t₁ t₂ → _∼v_ {R = R} ts₁ ts₂ → (t₁ ▹ ts₁) ∼v (t₂ ▹ ts₂)

pattern ∼⟨⟨_,_⟩⟩∼ a b = ∼▹ a (∼▹ b ∼⟨⟩)

_* : ∀ {l₀ l₁ I} {A : I → Set l₀} (R : IRel A l₁) → {is : List I} →
     Rel (HVec A is) (l₀ ⊔ l₁)
R * = _∼v_ {R = R}

{- Alternatively we can take a relation R over A as a predicate over A × A;
  under this view, the extension of R is the same as the extension of the
  predicate over the zipped vectors.
-}
private
  _*' : ∀ {l₀ l₁ I} {A : I → Set l₀} (R : IRel A l₁) → {is : List I} → Rel (HVec A is) (l₀ ⊔ l₁)
  _*' {A = A} R {is} a b = _⇨v_ {A = λ i → A i × A i} (λ { {i} (a , b) → R {i} a b} ) {is} (zip a b)

  from : ∀ {l₀ l₁ I} {is} {A : I → Set l₀} (R : IRel A l₁) → (as as' : HVec A is) → (R *') as as' → (R *) as as'
  from {is = []} R ⟨⟩ ⟨⟩ ⇨v⟨⟩ = ∼⟨⟩
  from {is = x ∷ is} R (v ▹ as) (v₁ ▹ as') (⇨v▹ {v = .v , .v₁} pv rel) = ∼▹ pv (from R as as' rel)

  to : ∀ {l₀ l₁ I} {is} {A : I → Set l₀} (R : IRel A l₁) → (as as' : HVec A is) → (R *) as as' → (R *') as as'
  to {is = []} R ⟨⟩ ⟨⟩ ∼⟨⟩ = ⇨v⟨⟩
  to {is = x ∷ is} R (v ▹ as) (v₁ ▹ as') (∼▹ x₁ rel) = ⇨v▹ x₁ (to R as as' rel)

map∼v : ∀ {l₀ l₁ l₂ I} {A : I → Set l₀}
        {R : IRel A l₁} {R' : IRel A l₂}
        {is : List I} {vs vs' : HVec A is} →
        (f : {i : I} {a a' : A i} → R {i} a a' → R' {i} a a') →
        _∼v_ {R = R} vs vs' → _∼v_ {R = R'} vs vs'
map∼v f ∼⟨⟩ = ∼⟨⟩
map∼v f (∼▹ vRv' vs≈Rvs') = ∼▹ (f vRv') (map∼v f vs≈Rvs')

fmap∼v : ∀ {l₀ l₁ l₂ l₃ I} {A : I → Set l₀} {B : I → Set l₃}
        {R : IRel A l₁} {R' : IRel B l₂}
        {f : {i : I} → A i → B i} →
        {is : List I} {vs vs' : HVec A is} →
        (F : {i : I} {a a' : A i} → R {i} a a' → R' {i} (f a) (f a')) →
        _∼v_ {R = R} vs vs' → _∼v_ {R = R'} (map (λ i → f {i}) vs) (map (λ i → f {i}) vs')
fmap∼v F ∼⟨⟩ = ∼⟨⟩
fmap∼v F (∼▹ vRv' vs≈Rvs') = ∼▹ (F vRv') (fmap∼v F vs≈Rvs')

~v-pointwise : ∀ {l₀} {l₁} {I : Set} {is : List I}
               {A : I → Set l₀} {R : IRel A l₁} →
               {vs₁ vs₂ : HVec A is} → _∼v_ {R = R} vs₁ vs₂ →
               (n : Fin (length is)) → R {is ‼ n} (vs₁ ‼v n) (vs₂ ‼v n)
~v-pointwise (∼▹ v₁∼v₂ _) zero = v₁∼v₂
~v-pointwise (∼▹ _ eq) (suc n) = ~v-pointwise eq n

∼↑v : ∀ {l₀ l₁ I} {A : I -> Set l₀} {is : List I} {R : IRel A l₁}
        {f : (i : I) → A i → A i} →
        (P : (i : I) → (a : A i) → R {i} a (f i a)) →
        (vs : HVec A is) → _∼v_ {R = R} vs (map f vs)
∼↑v P ⟨⟩ = ∼⟨⟩
∼↑v {is = i ∷ is} P (v ▹ vs) = ∼▹ (P i v) (∼↑v P vs)

{- Reindexing -}
reindex : ∀ {l} {I I' : Set}
          (fᵢ : I → I') → {A : I' → Set l} → {is : List I} →
          HVec (A ∘ fᵢ) is → HVec A (lmap fᵢ is)
reindex fᵢ ⟨⟩ = ⟨⟩
reindex fᵢ (v ▹ vs) = v ▹ reindex fᵢ vs

-- Reindex of extension of predicates
⇨v-reindex : ∀ {l₀ l₁ I I' is} {A : I' → Set l₀} {P : IPred A l₁} →
             (fᵢ : I → I') → {vs : HVec (A ∘ fᵢ) is} →
             (λ {i} → P {fᵢ i}) ⇨v vs → (λ {i} → P {i}) ⇨v (reindex fᵢ vs)
⇨v-reindex fᵢ ⇨v⟨⟩ = ⇨v⟨⟩
⇨v-reindex fᵢ (⇨v▹ pv p) = ⇨v▹ pv (⇨v-reindex fᵢ p)

-- Reindex of extension of relations
∼v-reindex : ∀ {l₀ l₁} {I I' : Set} {is : List I} →
             {A : I' → Set l₀} {R : IRel A l₁} →
             (fᵢ : I → I') → {vs₁ vs₂ : HVec (A ∘ fᵢ) is} →
             _∼v_ {R = λ {i} → R {fᵢ i}} vs₁ vs₂ →
             _∼v_ {I = I'} {R = λ {i} → R {i}} (reindex fᵢ vs₁) (reindex fᵢ vs₂)
∼v-reindex fₛ ∼⟨⟩ = ∼⟨⟩
∼v-reindex fᵢ (∼▹ v₁∼v₂ eq) = ∼▹ v₁∼v₂ (∼v-reindex fᵢ eq)

-- Mapping reindexed vectors
mapReindex : ∀ {l₀ l₁ I I' is} {A₀ : I' → Set l₀} {A₁ : I' → Set l₁} →
              (fᵢ : I → I') → (h : (i : I') → A₀ i → A₁ i) →
              (vs : HVec (A₀ ∘ fᵢ) is) →
              map h (reindex fᵢ vs) PE.≡ reindex fᵢ (map (h ∘ fᵢ) vs)
mapReindex {is = []} fᵢ h ⟨⟩ = PE.refl
mapReindex {is = i₀ ∷ is} fᵢ h (v ▹ vs) = PE.cong (λ vs' → h (fᵢ i₀) v ▹ vs')
                                               (mapReindex fᵢ h vs)

-- Other properties

-- Functoriality of map
map-id : ∀ {l₀ I} {A : I → Set l₀} {is : List I} →
         map (λ _ a → a) PE.≗ id {A = HVec A is}
map-id ⟨⟩ = PE.refl
map-id (v ▹ vs) = PE.cong (_▹_ v) (map-id vs)

map-compose : ∀ {l₀ l₁ l₂ I is} {A₀ : I → Set l₀} {A₁ : I → Set l₁}
              {A₂ : I → Set l₂} →
              (m  : (i : I) → (A₀ i) → (A₁ i)) →
              (m' : (i : I) → (A₁ i) → (A₂ i)) →
              (map m' ∘ map m) PE.≗ map {A = A₀} {is = is} (λ s' → m' s' ∘ m s')
map-compose m m' ⟨⟩ = PE.refl
map-compose m m' (v₀ ▹ vs) = PE.cong₂ (_▹_) PE.refl (map-compose m m' vs)


-- Setoid of heterogeneous vectors
open Setoid

vecSetoid : ∀ {l₁ l₂ I}→ (A : I → Setoid l₁ l₂) → IndexedSetoid (List I) _ _
vecSetoid {I = I} A = record
  { Carrierᵢ = HVec (Carrier ∘ A)
  ; _≈ᵢ_ = _∼v_ {R = λ {i} → _≈_ (A i)}
  ; isEquivalenceᵢ = record { reflᵢ = refl~v
                           ; symᵢ = sym~v
                           ; transᵢ = trans~v
                           }
  }
  where
    open Setoid
    refl~v : {is : List I} → Reflexive (_∼v_ {is = is})
    refl~v {[]} {⟨⟩} = ∼⟨⟩
    refl~v {i ∷ is} {v ▹ vs} = ∼▹ (refl (A i)) (refl~v {is})

    sym~v : {is : List I} → Symmetric (_∼v_ {is = is})
    sym~v {[]} {⟨⟩} ∼⟨⟩ = ∼⟨⟩
    sym~v {i ∷ is} {v ▹ vs} (∼▹ v≈w vs≈ws) = ∼▹ (sym (A i) v≈w) (sym~v {is} vs≈ws)

    trans~v : {is : List I} → Transitive (_∼v_ {is = is})
    trans~v {[]} {⟨⟩} ∼⟨⟩ ∼⟨⟩ = ∼⟨⟩
    trans~v {i ∷ _} (∼▹ v≈w vs≈ws) (∼▹ w≈z ws≈zs) = ∼▹ (trans (A i) v≈w w≈z)
                                                         (trans~v vs≈ws ws≈zs)


▹inj : ∀ {l₀ I} {A : I → Set l₀} {is i} {v v' : A i} {vs vs' : HVec A is}  →
       v ▹ vs PE.≡ v' ▹ vs' → v PE.≡ v' × vs PE.≡ vs'
▹inj PE.refl = PE.refl , PE.refl


≡vec : ∀ {l₀ I} {A : I → Set l₀} {is}  → {ts₁ ts₂ : HVec A is} →
        _∼v_ {R = λ {_} → PE._≡_} ts₁ ts₂ →
        ts₁ PE.≡ ts₂
≡vec {ts₁ = ⟨⟩} {⟨⟩} ≈⟨⟩ = PE.refl
≡vec {ts₁ = t ▹ ts₁} {.t ▹ ts₂} (∼▹ PE.refl ts₁≈ts₂) = PE.cong (t ▹_) (≡vec ts₁≈ts₂)

≡to∼v : ∀ {l₀ l₁ I} {A : I → Set l₀} {R : IRel A l₁} {is : List I}
        {vs vs' : HVec A is} → ((i : I) → IsEquivalence (R {i})) →
        vs PE.≡ vs' → _∼v_ {R = R} vs vs'
≡to∼v {vs = ⟨⟩} {⟨⟩} _ _ = ∼⟨⟩
≡to∼v {R = R} {vs = _▹_ {i} v vs} {v' ▹ vs'} ise eq =
  ∼▹ (PE.subst (λ v~ → R {i} v v~) v≡v' (irefl (ise i))) (≡to∼v ise vs≡vs')
  where
  open IsEquivalence renaming (refl to irefl)
  v≡v' : v PE.≡ v'
  v≡v' = proj₁ (▹inj eq)
  vs≡vs' : vs PE.≡ vs'
  vs≡vs' = proj₂ (▹inj eq)

-- Adapted from the stdlib.
module _ {a i} {I : Set i} where
  open IndexedSetoid
  _atₛ_ : ∀ {ℓ} → IndexedSetoid I a ℓ → I → Setoid a ℓ
  _atₛ_ S index = record
    { Carrier       = S.Carrierᵢ index
    ; _≈_           = S._≈ᵢ_ {index}
    ; isEquivalence = record { refl = S.reflᵢ {index}
                             ; sym = S.symᵢ {index}
                             ; trans = S.transᵢ {index} }
    }
    where module S = IndexedSetoid S


_✳_ : ∀ {l₁ l₂} → {I : Set} → (A : I → Setoid l₁ l₂) → List I → Setoid l₁ (l₁ ⊔ l₂)
_✳_ {I = I} A is = (vecSetoid {I = I} A) atₛ is

mapₛ : ∀ {l₁ l₂ l₃ l₄ : Level} {I : Set} →
         {A : I → Setoid l₁ l₂} {B : I → Setoid l₃ l₄} →
         {is : List I} (f : {i : I} → A i ⟶ B i) →
         A ✳ is ⟶ B ✳ is
mapₛ {A} {is = is} f = record
  { _⟨$⟩_ = map (λ i → f {i} ⟨$⟩_)
  ; cong = fmap∼v (Π.cong f)
  }
