{-# OPTIONS --universe-polymorphism #-}
module UnivAlgebra where

open import Relation.Binary
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Nat hiding (_⊔_)
open import Data.Vec
open import Data.Product hiding (map)
open import Function
open import Data.Unit hiding (setoid)
open import Data.Bool
open import Relation.Binary.PropositionalEquality


{- Dado un conjunto A y un número n, construye
   el tipo A × A × ... × A, donde A aparece n+1 veces -}
mkProd : ∀ {l} (A : Set l) → ℕ → Set l
mkProd A zero = Lift Unit
mkProd A (suc n) = mkProd A n × A

{-
data Arity {l} : (A : Set l) → ℕ → Set l
  constant : Arity A zero
  fun      : (n : ℕ) → Arity A zero → 
-}

{-
  Tipo de pares que contenien en el primer
  componente el número n y en el segundo la n+1-upla
-}
NProd : ∀ {l} → (A : Set l) → Set l
NProd A = Σ ℕ (λ n → mkProd A n)


open Setoid

record Signature : Set₁ where
  field
    sorts : Set
    funcs : Set
    -- Aridad. Para cada símbolo de función obtenemos la cantidad de 
    -- parámetros y su tipo. El tipo estará representado por una tupla de sorts.
    arity : funcs → NProd sorts × sorts

open Signature

{- 
   dado un conjunto A, un par (n , (a₁,a₂ ....,aₙ₊₁)) donde cada aᵢ ∈ A y
   una función i de A en algún Set l₂, retorna el tipo formado por aplicar
   la función a cada elemento de la tupla: i a₁ × i a₂ × .... × i aₙ₊₁
-}


MapP : ∀ {l₁} {l₂} → (A : Set l₁) → NProd A → (A → Set l₂) → Set l₂
MapP A (zero , lift unit) i = Lift Unit
MapP A (suc n , (args , s)) i = MapP A (n , args) i × i s

map× : ∀ {l₁} {l₂} {B B' : Set l₂} {A : Set l₁} {i : A → Set l₂} {i' : A → Set l₂} →
                   (nargs : NProd A) →
                   (as : MapP A nargs i) → (m : (s : A) → (i s) → (i' s)) →
                   MapP A nargs i'
map× (zero , lift unit) (lift unit) m = lift unit
map× {B = B} {B' = B'} (suc n , args , a) (iargs , ia) m =
                              map× {B = B} {B' = B'}
                                   (n , args) iargs m , m a ia

IFun : ∀ {l₁} {l₂} → (A : Set l₁) → (NProd A × A) → (A → Set l₂) → Set l₂
IFun A (nargs , a) i = MapP A nargs i → i a


record Algebra {l₁ l₂ : Level} (S : Signature) : 
                             Set (lsuc (l₁ ⊔ l₂)) where
  field
    isorts   : (s : sorts S) → Setoid l₁ l₂
    ifuns    : (f : funcs S) →
               IFun {lzero} {l₁} (sorts S) (arity S f) (Carrier ∘ isorts)
                                                   

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
homPreserv S A A' m f = (as : MapP (sorts S) targs (Carrier ∘ isorts A)) →
                        _≈_ (isorts A' tgtf) (m tgtf (ifuns A f as))
                                             (ifuns A' f (map× {B = (Carrier $ isorts A tgtf)}
                                                               {B' = (Carrier $ isorts A' tgtf)}
                                                               targs as m))
  where tgtf = proj₂ $ arity S f
        targs = proj₁ $ arity S f


record Homomorphism {l₁ l₂ : Level} 
                    (S : Signature) (A A' : Algebra {l₁} {l₂} S) : 
                                    Set (lsuc (l₁ ⊔ l₂)) where
  field
    -- Familia de funciones
    morphs  : (s : sorts S) → Carrier (isorts A s) → 
                              Carrier (isorts A' s)
    -- Propiedad de preservación de operaciones.
    preserv : (f : funcs S) → homPreserv S A A' morphs f


-- -- Pregunta: podemos definir composición de homos y probar que también lo es?

-- -- Igualdad de homomorfismos

open Homomorphism

data _≈ₕ_ {l₁ l₂} {S} {A A' : Algebra {l₁} {l₂} S} : 
          (H H' : Homomorphism S A A') → Set (lsuc (l₁ ⊔ l₂)) where
  ext : (H H' : Homomorphism S A A') → (s : sorts S) → (a b : Carrier (isorts A s)) →
        _≈_ (isorts A s) a b → _≈_ (isorts A' s) (morphs H s a) (morphs H' s b) →
        H ≈ₕ H'

-- Composición de homomorfismos

_∘ₕ_ : ∀ {l₁ l₂} {S} {A₀ A₁ A₂ : Algebra {l₁} {l₂} S} →
       (H₁ : Homomorphism S A₁ A₂) → (H₀ : Homomorphism S A₀ A₁) →
       Homomorphism S A₀ A₂
_∘ₕ_ {l₁} {l₂} {S} {A₀} {A₁} {A₂} H₁ H₀ =
               record { morphs = comp
                      ; preserv = {!!} }
  where comp = λ s → morphs H₁ s ∘ morphs H₀ s
        pres : (f : funcs S) → homPreserv S A₁ A₂ (morphs H₁) f →
                               homPreserv S A₀ A₁ (morphs H₀) f →
                               homPreserv S A₀ A₂ comp f
        pres f p₁ p₀ = {!!}

{-
_∘ₕ_ : ∀ {l₁ l₂} {S} {A₀ A₁ A₂ : Algebra {l₁} {l₂} S} →
       (H₁ : Homomorphism S A₁ A₂) → (H₀ : Homomorphism S A₀ A₁) →
       Homomorphism S A₀ A₂
_∘ₕ_ {l₁} {l₂} {S} {A₀} {A₁} {A₂} H₁ H₀ = record { morphs = comp
                                        ; preserv = {!!} }
  where comp : (s : sorts S) → Carrier (isorts A₀ s) → Carrier (isorts A₂ s)
        comp s a = morphs H₁ s (morphs H₀ s a)
        pres : (f : funcs S) → homPreserv S A₁ A₂ (morphs H₁) f →
                                homPreserv S A₀ A₁ (morphs H₀) f →
                                homPreserv S A₀ A₂ comp f
        pres f p₁ p₀ with arity S f | inspect (arity S) f
        pres f (lift p₁) (lift p₀) | zero , s | [ eq ] = lift (Setoid.trans (isorts A₂ s) {!!} {!cong ? ?!}) -- 
        pres f p₁ p₀ | suc n , ss , s | i = {!!}
-}
