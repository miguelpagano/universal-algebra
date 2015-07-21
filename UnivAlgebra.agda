{-# OPTIONS --universe-polymorphism #-}
module UnivAlgebra where

open import Relation.Binary
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Nat hiding (_⊔_)
open import Data.Vec
open import Data.Product hiding (map)
open import Function
open import Function.Equality renaming (_∘_ to _∘ₛ_)
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

ftgt : ∀ {S : Signature} → (f : funcs S) → sorts S
ftgt {S} f = proj₂ (arity S f)

fdom : ∀ {S : Signature} → (f : funcs S) → NProd (sorts S)
fdom {S} f = proj₁ (arity S f)



{- 
   dado un conjunto A, un par (n , (a₁,a₂ ....,aₙ₊₁)) donde cada aᵢ ∈ A y
   una función i de A en algún Set l₂, retorna el tipo formado por aplicar
   la función a cada elemento de la tupla: i a₁ × i a₂ × .... × i aₙ₊₁
-}


MapP : ∀ {l₁} {l₂} → (A : Set l₁) → NProd A → (A → Set l₂) → Set l₂
MapP A (zero , lift unit) i = Lift Unit
MapP A (suc n , (args , s)) i = MapP A (n , args) i × i s

map× : ∀ {lₐ} {l₁} {l₂} {B B' : Setoid l₁ l₂} {A : Set lₐ} {i : A → Setoid l₁ l₂} {i' : A → Setoid l₁ l₂} →
                   (nargs : NProd A) →
                   (as : MapP A nargs (Carrier ∘ i)) → (m : (s : A) → (i s) ⟶ (i' s)) →
                   MapP A nargs (Carrier ∘ i')
map× (zero , lift unit) (lift unit) m = lift unit
map× {B = B} {B' = B'} (suc n , args , a) (iargs , ia) m =
                              map× {B = B} {B' = B'}
                                   (n , args) iargs m , m a ⟨$⟩ ia

IFun : ∀ {l₁} {l₂} → (A : Set l₁) → (NProd A × A) → (A → Set l₂) → Set l₂
IFun A (nargs , a) i = MapP A nargs i → i a


record Algebra {l₁ l₂ : Level} (S : Signature) : 
                             Set (lsuc (l₁ ⊔ l₂)) where
  field
    isorts   : (s : sorts S) → Setoid l₁ l₂
    ifuns    : (f : funcs S) →
               IFun {lzero} {l₁} (sorts S) (arity S f) (Carrier ∘ isorts)

open Algebra


-- Definición de la propiedad de preservación en el Homomorfismo entre A y A'
homPreserv : ∀ {l₁ l₂} → (S : Signature) → (A : Algebra {l₁} {l₂} S) →
                         (A' : Algebra {l₁} {l₂} S) →
                         ((s : sorts S) → isorts A s ⟶ isorts A' s) →
                         (f : funcs S) → Set (l₂ ⊔ l₁)
homPreserv S A A' m f = (as : MapP (sorts S) targs (Carrier ∘ isorts A)) →
                        _≈_ (isorts A' tgtf) (m tgtf ⟨$⟩ (ifuns A f as))
                                             (ifuns A' f (map× {B = (isorts A tgtf)}
                                                               {B' = (isorts A' tgtf)}
                                                               targs as m))
  where tgtf = proj₂ $ arity S f
        targs = proj₁ $ arity S f


record Homomorphism {l₁ l₂ : Level} 
                    (S : Signature) (A A' : Algebra {l₁} {l₂} S) : 
                                    Set (lsuc (l₁ ⊔ l₂)) where
  field
    -- Familia de funciones
    morphs  : (s : sorts S) → isorts A s ⟶
                              isorts A' s
    -- Propiedad de preservación de operaciones.
    preserv : (f : funcs S) → homPreserv S A A' morphs f


-- -- Pregunta: podemos definir composición de homos y probar que también lo es?

-- -- Igualdad de homomorfismos

open Homomorphism

data _≈ₕ_ {l₁ l₂} {S} {A A' : Algebra {l₁} {l₂} S} : 
          (H H' : Homomorphism S A A') → Set (lsuc (l₁ ⊔ l₂)) where
  ext : (H H' : Homomorphism S A A') → (s : sorts S) → (a b : Carrier (isorts A s)) →
        _≈_ (isorts A s) a b → _≈_ (isorts A' s) (morphs H s ⟨$⟩ a) (morphs H' s ⟨$⟩ b) →
        H ≈ₕ H'

-- Composición de homomorfismos

_∘ₕ_ : ∀ {l₁ l₂} {S} {A₀ A₁ A₂ : Algebra {l₁} {l₂} S} →
       (H₁ : Homomorphism S A₁ A₂) → (H₀ : Homomorphism S A₀ A₁) →
       Homomorphism S A₀ A₂
_∘ₕ_ {l₁} {l₂} {S} {A₀} {A₁} {A₂} H₁ H₀ =
               record { morphs = comp
                      ; preserv = pres }
  where comp = λ s → morphs H₁ s ∘ₛ morphs H₀ s
        pres : (f : funcs S) → homPreserv S A₀ A₂ comp f
        pres f  = λ as → Setoid.trans (isorts A₂ s) (Π.cong (morphs H₁ s) (p₀ as))
                         (Setoid.trans (isorts A₂ s) (p₁ (map× args as (morphs H₀)))
                                                     (compMap× as))
          where p₁ = preserv H₁ f
                p₀ = preserv H₀ f
                s = ftgt {S} f
                args = fdom {S} f
                compMap× : (as : MapP (sorts S) args (Carrier ∘ isorts A₀)) → 
                           _≈_ (isorts A₂ s)
                           ((ifuns A₂ f) (map× args (map× args as (morphs H₀)) (morphs H₁)))
                           ((ifuns A₂ f) (map× args as comp))
                compMap× = {!!}

{-
                 Esta seria la prueba pres en un lenguaje mas ameno:

                 p₀ :   H₀ fₐ₀ as ≈ₐ₁ fₐ₁ (map× H₀ as)

                 p₁ :   H₁ fₐ₁ as ≈ₐ₂ fₐ₂ (map× H₁ as)


                    Hₒ fₐ₀ as ≈ₐ₂ fₐ₂ (map× Hₒ as)

                   si Hᵢ es una funcion que preserva igualdad, entonces:

                   H₁ (H₀ fₐ₀ as) ≈ₐ₁ H₁ (fₐ₁ (map× H₀ as)) (por p₀ y cong)

                   luego H₁ (fₐ₁ (map× H₀ as)) ≈ₐ₂ fₐ₂ (map× H₁ (map× H₀ as)) ($

                   y luego deberíamos ver que map× H₁ ∘ map× H₀ ≡ map× Hₒ y est$

 -}
