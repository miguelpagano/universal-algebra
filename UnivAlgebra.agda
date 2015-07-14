module UnivAlgebra where

open import Relation.Binary
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Nat hiding (_⊔_)
open import Data.Vec
open import Data.Product hiding (map)
open import Function
open import Data.Unit
open import Data.Bool

mkFun : ∀ {l} {n} → Vec (Set l) n → Set l → Set l
mkFun [] A = A
mkFun (x ∷ xs) A = x → mkFun xs A


mkProd : ∀ {l} (A : Set l) → ℕ → Set l
mkProd A zero = A
mkProd A (suc n) = mkProd A n × A

tgtf : ∀ {l} {A : Set l} {n} → mkProd A n → A
tgtf {n = zero} a = a
tgtf {n = suc n} t = proj₂ t

open Setoid

record Signature : Set₁ where
  field
    sorts : Set
    funcs : Set
    -- Aridad. Para cada símbolo de función obtenemos la cantidad de 
    -- parámetros y su tipo.
    arity : funcs → Σ ℕ (λ n → mkProd sorts n)

open Signature

mkProd' : ∀ {l₁} {l₂} → (A : Set l₁) → Σ ℕ (λ n → mkProd A n) → (A → Set l₂) → Set l₂
mkProd' A (zero , s) i = i s
mkProd' A ((suc n) , (args , s)) i = mkProd' A (n , args) i → i s


record Algebra {l₁ l₂ : Level} (S : Signature) : 
                             Set (lsuc (l₁ ⊔ l₂)) where
  field
    isorts   : (s : sorts S) → Setoid l₁ l₂
    ifuns    : (f : funcs S) →
               mkProd' {lzero} {l₁} (sorts S) (arity S f) (Carrier ∘ isorts)
                                                   

dom : ∀ {l} {A B : Set l} → (A → B) → Set l
dom {A = A} f = A

tgt : ∀ {l} {A B : Set l} → (A → B) → Set l
tgt {B = B} f = B

open Algebra


record Homomorphism {l₁ l₂ : Level} 
                    (S : Signature) (A A' : Algebra {l₁} {l₂} S) : 
                                    Set (lsuc (l₁ ⊔ l₂)) where
  field
    -- Familia de funciones
    morphs  : (s : sorts S) → Carrier (isorts A s) → 
                              Carrier (isorts A' s)
    -- Propiedad de preservación de operaciones. Parece que necesitamos
    -- vectores heterogéneos.
    preserv : (f : funcs S) → 
              case (arity S f) of
                   (λ { (zero , s) → _≈_ (isorts A' s) (morphs s
                                              {!ifuns A f!}) {!!}
                 ; t → {!!} })
