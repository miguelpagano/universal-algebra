module VecH where

open import Data.List
open import Relation.Binary
open import Level
open import Data.Fin
open import Function
open import Relation.Binary.PropositionalEquality

{-
Vectores Heterogéneos. Dado un conjunto de índices I y
una familia A indexada en I, un vector heterogéneo con índices (i₁,...,iₙ)
tendrá elementos (a₁,...,aₙ) donde cada aᵢ : A iᵢ
-}
data VecH {l} (I : Set) (A : I -> Set l) : List I → Set l where
  ⟨⟩  : VecH I A []
  _▹_ : ∀ {i} {is} → (v : A i) → (vs : VecH I A is) → VecH I A (i ∷ is)

{-
Extensión de una relación a vectores.
-}
data _∼v_ {l₀ l₁} {I : Set} {A : I → Set l₀} {R : (i : I) → Rel (A i) l₁} :
          {is : List I} → (ts₁ : VecH I A is) →
                          (ts₂ : VecH I A is) → Set (l₀ ⊔ l₁) where
     ∼⟨⟩ : ⟨⟩ ∼v ⟨⟩
     ∼▹  : ∀ {i} {is} {t₁} {t₂} {ts₁ : VecH I A is} {ts₂ : VecH I A is} →
           R i t₁ t₂ → _∼v_ {R = R} ts₁ ts₂ → (t₁ ▹ ts₁) ∼v (t₂ ▹ ts₂)


{- 
map en vectores heterogéneos
-}
mapV : ∀ {l₀} {l₁} {I : Set} {A : I → Set l₀} {A' : I → Set l₁} →
         (f : (i : I) → (A i) → (A' i)) → (is : List I) →
         (vs : VecH I A is) → VecH I A' is
mapV f [] ⟨⟩ = ⟨⟩
mapV f (i₀ ∷ is) (v₀ ▹ vs) = f i₀ v₀ ▹ mapV f is vs


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
             (fᵢ : I → I') → (vs₁ vs₂ : VecH I (A ∘ fᵢ) is) →
             _∼v_ {R = R ∘ fᵢ} vs₁ vs₂ →
             _∼v_ {I = I'} {R = R}
                  (vecTransf fᵢ A is vs₁)
                  (vecTransf fᵢ A is vs₂)
∼vtransf fₛ ⟨⟩ ⟨⟩ ∼⟨⟩ = ∼⟨⟩
∼vtransf fᵢ (v₁ ▹ vs₁) (v₂ ▹ vs₂) (∼▹ v₁∼v₂ eq) =
                                            ∼▹ v₁∼v₂ (∼vtransf fᵢ vs₁ vs₂ eq)


{- Mapear una función en un vector transformado es lo mismo
   que transformar el vector mapeado.
-}
≡maptransf : ∀ {l₀} {l₁} {I I' : Set}
              (fᵢ : I → I') →
              (A₀ : I' → Set l₀) → (A₁ : I' → Set l₁) →
              (h : (i : I') → A₀ i → A₁ i) →
              (is : List I) → (vs : VecH I (A₀ ∘ fᵢ) is) →
              mapV h (map fᵢ is) (vecTransf fᵢ A₀ is vs) ≡
              vecTransf fᵢ A₁ is (mapV (h ∘ fᵢ) is vs)
≡maptransf fᵢ A₀ A₁ h [] ⟨⟩ = refl
≡maptransf fᵢ A₀ A₁ h (i₀ ∷ is) (v ▹ vs) = cong (λ vs' → h (fᵢ i₀) v ▹ vs')
                                                  (≡maptransf fᵢ A₀ A₁ h is vs)


-- Si dos vectores vs₁ y vs₂ son iguales, entonces para todo n menor al tamaño
-- vs₁ ‼v n ≈ vs₂ ‼v n
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
propMapVComp : ∀ {l₀ l₁ l₂} {I : Set}
                 {A₀ : I → Set l₀} {A₁ : I → Set l₁}
                 {A₂ : I → Set l₂} → (is : List I) →
                 (vs : VecH I A₀ is) →
                 (m : (i : I) → (A₀ i) → (A₁ i)) →
                 (m' : (i : I) → (A₁ i) → (A₂ i)) →
                 mapV m' is (mapV m is vs)
                 ≡
                 mapV (λ s' → m' s' ∘ m s') is vs
propMapVComp [] ⟨⟩ m m' = refl
propMapVComp (i₀ ∷ is) (v₀ ▹ vs) m m' =
                   cong₂ (λ x y → x ▹ y) refl
                         (propMapVComp is vs m m')

