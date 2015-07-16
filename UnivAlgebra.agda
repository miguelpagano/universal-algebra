module UnivAlgebra where

open import Relation.Binary
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Nat hiding (_⊔_)
open import Data.Vec
open import Data.Product hiding (map)
open import Function
open import Data.Unit
open import Data.Bool
open import Relation.Binary.PropositionalEquality


{- Dado un conjunto A y un número n, construye
   el tipo A × A × ... × A, donde A aparece n+1 veces -}
mkProd : ∀ {l} (A : Set l) → ℕ → Set l
mkProd A zero = A
mkProd A (suc n) = mkProd A n × A

{-
  Tipo de pares que contenien en el primer
  componente el número n y en el segundo la n+1-upla
-}
NProd : ∀ {l} → (A : Set l) → Set l
NProd A = Σ ℕ (λ n → mkProd A n)


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
    arity : funcs → NProd sorts

open Signature

{- 
   dado un conjunto A, un par (n , (a₁,a₂ ....,aₙ₊₁)) donde cada aᵢ ∈ A y
   una función i de A en algún Set l₂, retorna el tipo formado por aplicar
   la función a cada elemento de la tupla: i a₁ × i a₂ × .... × i aₙ₊₁
-}
MapP : ∀ {l₁} {l₂} → (A : Set l₁) → NProd A → (A → Set l₂) → Set l₂
MapP A (zero , s) i = i s
MapP A (suc n , (args , s)) i = MapP A (n , args) i × i s


map× : ∀ {l₁} {l₂} {B B' : Set l₂} {A : Set l₁} {i : A → Set l₂} {i' : A → Set l₂} →
                   (nargs : NProd A) →
                   (as : MapP A nargs i) → (m : (s : A) → (i s) → (i' s)) →
                   MapP A nargs i'
map× {B = B} {B' = B'} (zero , s) a m = m s a
map× {B = B} {B' = B'} (suc n , args , s) (as , a) m =
                                             (map× {B = B}
                                                   {B' = B'}
                                                   (n , args) as m) , (m s a)


{-
   dado un conjunto A, un par (n , (a₁,a₂ ....,aₙ₊₁)) donde cada aᵢ ∈ A y
   una función i de A en algún Set l₂, retorna el tipo
   i a₁ × i a₂ × .... × i aₙ → i aₙ₊₁
-}
Fun : ∀ {l₁} {l₂} → (A : Set l₁) → NProd A → (A → Set l₂) → Set l₂
Fun A (zero , s) i = i s
Fun A ((suc n) , (args , s)) i = MapP A (n , args) i → i s


record Algebra {l₁ l₂ : Level} (S : Signature) : 
                             Set (lsuc (l₁ ⊔ l₂)) where
  field
    isorts   : (s : sorts S) → Setoid l₁ l₂
    ifuns    : (f : funcs S) →
               Fun {lzero} {l₁} (sorts S) (arity S f) (Carrier ∘ isorts)
                                                   

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
  where p : ∀ {Ã : Algebra {l₁} {l₂} S} →
            arity S f ≡ (zero , s) →
            Fun (sorts S) (arity S f) (Carrier ∘ isorts Ã) →
            Carrier (isorts Ã s)
        p ep if rewrite ep = if
homPreserv {l₁} {l₂} S A A' m f | suc n , (args , s) | [ eq ] =
                                (as : MapP (sorts S) (n , args) (Carrier ∘ isorts A)) →
                                _≈_ (isorts A' s) (m s (p {A} eq (ifuns A f) as))
                                                  (p {A'} eq (ifuns A' f)
                                                    (map× {B = (Carrier $ isorts A s)}
                                                          {B' = (Carrier $ isorts A' s)}
                                                          (n , args) as m))
  where p : ∀ {Ã : Algebra {l₁} {l₂} S} →
            arity S f ≡ (suc n , (args , s)) →
            Fun (sorts S) (arity S f) (Carrier ∘ isorts Ã) →
            MapP (sorts S) (n , args) (Carrier ∘ isorts Ã) → Carrier (isorts Ã s)
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
