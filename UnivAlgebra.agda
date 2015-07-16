module UnivAlgebra where

open import Relation.Binary
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Nat hiding (_⊔_)
open import Data.Vec
open import Data.Product renaming (map to map×)
open import Function
open import Data.Unit
open import Data.Bool
open import Relation.Binary.PropositionalEquality


{- Dado un conjunto A y un número n, construye
   el tipo A × A × ... × A, donde A aparece n+1 veces -}
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
    -- parámetros y su tipo. El tipo estará representado por una tupla de sorts.
    arity : funcs → Σ ℕ (λ n → mkProd sorts n)

open Signature

{- 
   Dado un conjunto A, un par (n , (a₁,a₂ ....,aₙ) donde cada aᵢ ∈ A y
   una función i de A en algún Set l₂, retorna el tipo formado por aplicar
   la función a cada elemento de la tupla: i a₁ × i a₂ × .... × i aₙ
-}
mapP : ∀ {l₁} {l₂} → (A : Set l₁) → Σ ℕ (λ n → mkProd A n) → (A → Set l₂) → Set l₂
mapP A (zero , s) i = i s
mapP A (suc n , (args , s)) i = mapP A (n , args) i × i s


{-
   Dado un conjunto A, un par (n , (a₁,a₂ ....,a₃) donde cada aᵢ ∈ A y
   una función i de A en algún Set l₂, retorna el tipo
   i a₁ × i a₂ × .... × i a₍ₙ₋₁₎ → i aₙ
   
-}
mkProd' : ∀ {l₁} {l₂} → (A : Set l₁) → Σ ℕ (λ n → mkProd A n) → (A → Set l₂) → Set l₂
mkProd' A (zero , s) i = i s
mkProd' A ((suc n) , (args , s)) i = mapP A (n , args) i → i s


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


-- Definición de la propiedad de preservación en el Homomorfismo entre A y A'
homPreserv : ∀ {l₁ l₂} → (S : Signature) → (A : Algebra {l₁} {l₂} S) →
                         (A' : Algebra {l₁} {l₂} S) →
                         ((s : sorts S) → Carrier (isorts A s) → Carrier (isorts A' s)) →
                         (f : funcs S) → Set (l₂ ⊔ l₁)
homPreserv S A A' m f with (arity S f) | inspect (arity S) f
homPreserv {l₁} {l₂} S A A' m f | zero , s | [ eq ] = Lift {ℓ = l₁} (_≈_ (isorts A' s)
                                                             (m s (p {A} eq (ifuns A f)))
                                                           (p {A'} eq (ifuns A' f)))
                       -- EL TERMINO QUE ESTA ABAJO ES EL QUE VA PERO NO TIPA PORQUE ESTA
                       -- EN Set l₁
                       --  _≈_ (isorts A' s) (m s (p {A} eq (ifuns A f)))
                       --                         (p {A'} eq (ifuns A' f))
  where p : ∀ {Ã : Algebra {l₁} {l₂} S} →
            arity S f ≡ (zero , s) →
            mkProd' (sorts S) (arity S f) (Carrier ∘ isorts Ã) →
            Carrier (isorts Ã s)
        p ep if rewrite ep = if
homPreserv {l₁} {l₂} S A A' m f | suc n , (args , s) | [ eq ] =
                                (as : mapP (sorts S) (n , args) (Carrier ∘ isorts A)) →
                                _≈_ (isorts A' s) (m s (p {A} eq (ifuns A f) as))
                                                  (p {A'} eq (ifuns A' f) {!!})
  where p : ∀ {Ã : Algebra {l₁} {l₂} S} →
            arity S f ≡ (suc n , (args , s)) →
            mkProd' (sorts S) (arity S f) (Carrier ∘ isorts Ã) →
            mapP (sorts S) (n , args) (Carrier ∘ isorts Ã) → Carrier (isorts Ã s)
        p eq if rewrite eq = if


record Homomorphism {l₁ l₂ : Level} 
                    (S : Signature) (A A' : Algebra {l₁} {l₂} S) : 
                                    Set (lsuc (l₁ ⊔ l₂)) where
  field
    -- Familia de funciones
    morphs  : (s : sorts S) → Carrier (isorts A s) → 
                              Carrier (isorts A' s)
    -- Propiedad de preservación de operaciones.
    preserv : (f : funcs S) → homPreserv S A A' morphs f
