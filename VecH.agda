module VecH where

open import Data.List
open import Relation.Binary
open import Level
open import Data.Fin
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (map)

{-
Vectores Heterogéneos. Dado un conjunto de índices I y
una familia A indexada en I, un vector heterogéneo con índices (i₁,...,iₙ)
tendrá elementos (a₁,...,aₙ) donde cada aᵢ : A iᵢ
-}
data VecH {l} (I : Set) (A : I -> Set l) : List I → Set l where
  ⟨⟩  : VecH I A []
  _▹_ : ∀ {i} {is} → (v : A i) → (vs : VecH I A is) → VecH I A (i ∷ is)

{-
Indexar
-}
_‼_ : ∀ {l} {A : Set l} (xs : List A) → Fin (length xs) → A
[] ‼ ()
(x ∷ _) ‼ zero     = x
(_ ∷ xs) ‼ (suc n) = xs ‼ n


_‼v_ : ∀ {l} {I : Set} {is : List I} {A : I → Set l} →
             (vs : VecH I A is) → (n : Fin (length is)) → A (is ‼ n)
⟨⟩ ‼v ()
(v ▹ _) ‼v zero = v
(_ ▹ vs) ‼v suc n = vs ‼v n

infixr 6 _▹_
infixr 5 _∈_

{-
∈
-}
data _∈_ {l} {I} {A : I → Set l} : {i : I} {is : List I} → A i →
                                             VecH I A is → Set l where
  here  : ∀ {i} {is} {v : A i} {vs : VecH I A is} → v ∈ v ▹ vs
  there : ∀ {i i'} {is} {v : A i} {w : A i'} {vs : VecH I A is}
                   (v∈vs : v ∈ vs) → v ∈ w ▹ vs


{-
Extensión de un predicado a vectores.
-}
_⇨v_ : ∀ {l₀ l₁} {I : Set} {A : I → Set l₀} → (P : (i : I) → A i → Set l₁) →
                {is : List I} → VecH I A is → Set (l₀ ⊔ l₁)
_⇨v_ {I = I} {A} P {is} vs = VecH I (λ i → Σ[ ai ∈ (A i) ] (P i ai)) is

{-
     ⇨v⟨⟩ : P ⇨v ⟨⟩
     ⇨v▹ : ∀ {i} {is} {t₁} {ts₁ : VecH I A is} →
              P i t₁ → P ⇨v ts₁ → P ⇨v (t₁ ▹ ts₁)
-}
{-
Extensión de una relación a vectores.
-}
data _∼v_ {l₀ l₁} {I : Set} {A : I → Set l₀} {R : (i : I) → Rel (A i) l₁} :
          {is : List I} → Rel (VecH I A is) (l₀ ⊔ l₁) where
     ∼⟨⟩ : ⟨⟩ ∼v ⟨⟩
     ∼▹  : ∀ {i} {is} {t₁} {t₂} {ts₁ : VecH I A is} {ts₂ : VecH I A is} →
           R i t₁ t₂ → _∼v_ {R = R} ts₁ ts₂ → (t₁ ▹ ts₁) ∼v (t₂ ▹ ts₂)


{- 
map en vectores heterogéneos
-}
mapV : ∀ {l₀} {l₁} {I : Set} {A : I → Set l₀} {A' : I → Set l₁} {is : List I} →
         (f : (i : I) → (A i) → (A' i)) → (vs : VecH I A is) → VecH I A' is
mapV {is = []} f ⟨⟩ = ⟨⟩
mapV {is = i₀ ∷ is} f (v₀ ▹ vs) = f i₀ v₀ ▹ mapV f vs


{-
Transformación de un vector con índices en I a 
un vector con índices en I'.
-}
vecTransf : ∀ {l} {I I' : Set}
              (fᵢ : I → I') → (A : I' → Set l) → (is : List I) →
              VecH I (A ∘ fᵢ) is → VecH I' A (map fᵢ is)
vecTransf fᵢ A .[] ⟨⟩ = ⟨⟩
vecTransf fᵢ A (_ ∷ is) (v ▹ vs) = v ▹ vecTransf fᵢ A is vs


{-
Si dos vectores están relacionados, sus transformados también
lo están.
-}
∼vtransf : ∀ {l₀} {l₁} {I I' : Set} {is : List I}
             {A : I' → Set l₀} {R : (i : I') → Rel (A i) l₁} →
             (fᵢ : I → I') → {vs₁ vs₂ : VecH I (A ∘ fᵢ) is} →
             _∼v_ {R = R ∘ fᵢ} vs₁ vs₂ →
             _∼v_ {I = I'} {R = R}
                  (vecTransf fᵢ A is vs₁)
                  (vecTransf fᵢ A is vs₂)
∼vtransf fₛ ∼⟨⟩ = ∼⟨⟩
∼vtransf fᵢ (∼▹ v₁∼v₂ eq) = ∼▹ v₁∼v₂ (∼vtransf fᵢ eq)


{- Mapear una función en un vector transformado es lo mismo
   que transformar el vector mapeado.
-}
≡maptransf : ∀ {l₀} {l₁} {I I' : Set}
              (fᵢ : I → I') →
              (A₀ : I' → Set l₀) → (A₁ : I' → Set l₁) →
              (h : (i : I') → A₀ i → A₁ i) →
              (is : List I) → (vs : VecH I (A₀ ∘ fᵢ) is) →
              mapV h (vecTransf fᵢ A₀ is vs) ≡
              vecTransf fᵢ A₁ is (mapV (h ∘ fᵢ) vs)
≡maptransf fᵢ A₀ A₁ h [] ⟨⟩ = refl
≡maptransf fᵢ A₀ A₁ h (i₀ ∷ is) (v ▹ vs) = cong (λ vs' → h (fᵢ i₀) v ▹ vs')
                                                  (≡maptransf fᵢ A₀ A₁ h is vs)


-- Si dos vectores vs₁ y vs₂ están relacionados, entonces para todo n menor
-- al tamaño vs₁ ‼v n ≈ vs₂ ‼v n
~v‼prop : ∀ {l₀} {l₁} {I : Set} {is : List I}
           {A : I → Set l₀} {R : (i : I) → Rel (A i) l₁} →
           (vs₁ vs₂ : VecH I A is) → _∼v_ {R = R} vs₁ vs₂ →
           (n : Fin (length is)) → R (is ‼ n) (vs₁ ‼v n) (vs₂ ‼v n)
~v‼prop ⟨⟩ .⟨⟩ ∼⟨⟩ ()
~v‼prop (v₁ ▹ vs₁) (v₂ ▹ vs₂) (∼▹ v₁∼v₂ eq) zero = v₁∼v₂
~v‼prop (v₁ ▹ vs₁) (v₂ ▹ vs₂) (∼▹ v₁∼v₂ eq) (suc n) = ~v‼prop vs₁ vs₂ eq n

{-
Map y composición
-}
propMapV∘ : ∀ {l₀ l₁ l₂} {I : Set}
              {A₀ : I → Set l₀} {A₁ : I → Set l₁}
              {A₂ : I → Set l₂} → (is : List I) →
              (vs : VecH I A₀ is) →
              (m : (i : I) → (A₀ i) → (A₁ i)) →
              (m' : (i : I) → (A₁ i) → (A₂ i)) →
              mapV m' (mapV m vs)
              ≡
              mapV (λ s' → m' s' ∘ m s') vs
propMapV∘ [] ⟨⟩ m m' = refl
propMapV∘ (i₀ ∷ is) (v₀ ▹ vs) m m' =
                   cong₂ (λ x y → x ▹ y) refl
                         (propMapV∘ is vs m m')

open Setoid

{-
Vector Setoid
-}
VecSet : ∀ {l₁ l₂} → (I : Set) → (A : I → Setoid l₁ l₂) →
                                 List I → Setoid _ _
VecSet I A is = record { Carrier = VecH I (λ i → Carrier $ A i) is
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
