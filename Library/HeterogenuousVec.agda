module HeterogenuousVec where

open import Data.List renaming (map to lmap)
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

pattern ⟨⟨_,_⟩⟩ a b = a ▹ (b ▹ ⟨⟩) 

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
map : ∀ {l₀ l₁ I} {A : I → Set l₀} {A' : I → Set l₁} {is : List I} →
         (f : (i : I) → (A i) → (A' i)) → (vs : HVec A is) → HVec A' is
map {is = []} f ⟨⟩ = ⟨⟩
map {is = i₀ ∷ is} f (v₀ ▹ vs) = f i₀ v₀ ▹ map f vs

mapId : ∀ {l₀ I} {A : I → Set l₀} {is : List I} →
          (vs : HVec A is) → map (λ _ a → a) vs ≡ vs
mapId ⟨⟩ = refl
mapId (v ▹ vs) = cong (_▹_ v) (mapId vs)


{-
Extension of predicates
-}
data _⇨v_ {l₀ l₁ I} {A : I → Set l₀} (P : (i : I) → A i → Set l₁) :
           {is : List I} → HVec A is → Set (l₀ ⊔ l₁) where
     ⇨v⟨⟩ : P ⇨v ⟨⟩
     ⇨v▹ : ∀ {i} {is} {v} {vs} → (pv : P i v) →
             (pvs : _⇨v_ P {is} vs) → P ⇨v (_▹_ {i = i} v vs)

⇨vtoΣ : ∀ {l₀ l₁ I} {A : I → Set l₀} {P : (i : I) → A i → Set l₁}
           {is} {vs : HVec A is} → P ⇨v vs → HVec (λ i → Σ[ a ∈ A i ] P i a) is
⇨vtoΣ ⇨v⟨⟩ = ⟨⟩
⇨vtoΣ (⇨v▹ {v = v} pv p⇨vs) = (v , pv) ▹ ⇨vtoΣ p⇨vs

map⇨v : ∀ {l₀ l₁ l₂ I is} {A : I → Set l₀} {vs : HVec A is} →
           (P : (i : I) → A i → Set l₁) → (P' : (i : I) → A i → Set l₂) →
           (f : ∀ {i'} {a : A i'} → P i' a → P' i' a) →
           P ⇨v vs → P' ⇨v vs
map⇨v P P' f ⇨v⟨⟩ = ⇨v⟨⟩
map⇨v P P' f (⇨v▹ pv pvs) = ⇨v▹ (f pv) (map⇨v P P' f pvs)
           

proj₁⇨v : ∀ {l₀ l₁ I} {A : I → Set l₀} {P : (i : I) → A i → Set l₁}
           {is} {vs : HVec A is} → P ⇨v vs → HVec A is
proj₁⇨v {vs = vs} _ = vs

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


{- PONER UN NOMBRE MEJOR PARA ESTO -}
∼↑v : ∀ {l₀ l₁ I} {A : I -> Set l₀} {is : List I} {R : (i : I) → Rel (A i) l₁}
        {f : (i : I) → A i → A i} →
        (P : (i : I) → (a : A i) → R i a (f i a)) →
        (vs : HVec A is) → _∼v_ {R = R} vs (map f vs)
∼↑v P ⟨⟩ = ∼⟨⟩
∼↑v {is = i ∷ is} P (v ▹ vs) = ∼▹ (P i v) (∼↑v P vs)
      

-- Reindexing


reindex : ∀ {l} {I I' : Set}
              (fᵢ : I → I') → {A : I' → Set l} → {is : List I} →
              HVec (A ∘ fᵢ) is → HVec A (lmap fᵢ is)
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
              map h (reindex fᵢ vs) ≡ reindex fᵢ (map (h ∘ fᵢ) vs)
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
              map m' (map m vs)
              ≡
              map (λ s' → m' s' ∘ m s') vs
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



▹inj : ∀ {l₀ I} {A : I → Set l₀} {is} {i : I} {vs vs' : HVec A is} {v v' : A i} →
       v ▹ vs ≡ v' ▹ vs' → v ≡ v' × vs ≡ vs'
▹inj _≡_.refl = _≡_.refl , _≡_.refl
       

≡to∼v : ∀ {l₀ l₁ I} {A : I → Set l₀} {R : (i : I) → Rel (A i) l₁} {is : List I}
        {vs : HVec A is} {vs' : HVec A is} → ((i : I) → IsEquivalence (R i)) →
        vs ≡ vs' →
        _∼v_ {R = R} vs vs'
≡to∼v {vs = ⟨⟩} {⟨⟩} ise eq = ∼⟨⟩
≡to∼v {R = R} {vs = _▹_ {i} {is} v vs} {vs' = v' ▹ vs'} ise eq =
              ∼▹ (subst (λ v~ → R i v v~) v≡v' (irefl (ise i))) (≡to∼v ise vs≡vs')
  where open IsEquivalence renaming (refl to irefl)
        v≡v' : v ≡ v'
        v≡v' = proj₁ (▹inj eq)
        vs≡vs' : vs ≡ vs'
        vs≡vs' = proj₂ (▹inj eq)

_✳_ : ∀ {l₁ l₂} → {I : Set} → (A : I → Setoid l₁ l₂) →
                                 List I → Setoid _ _
_✳_ {I = I} = HVecSet I
