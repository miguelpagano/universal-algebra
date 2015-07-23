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
open import Relation.Binary.PropositionalEquality as PE


{- Dado un conjunto A y un número n, construye
   el tipo A × A × ... × A, donde A aparece n veces.
   Si n = zero entonces retorna Lift Unit. -}
mkProd : ∀ {l} (A : Set l) → ℕ → Set l
mkProd A zero = Lift Unit
mkProd A (suc zero) = A
mkProd A (suc (suc n)) = mkProd A (suc n) × A

{-
  Tipo de pares que contenien en el primer
  componente el número n y en el segundo una n-upla de elementos de
  tipo A.
-}
NProd : ∀ {l} → (A : Set l) → Set l
NProd A = Σ ℕ (λ n → mkProd A n)

open Setoid

record Signature : Set₁ where
  field
    sorts : Set
    funcs : Set
    -- Aridad. Para cada símbolo de función obtenemos la cantidad de 
    -- parámetros y su tipo. El tipo estará representado por una tupla de sorts
    -- para el dominio y un sort para el codominio.
    arity : funcs → NProd sorts × sorts

open Signature


{-
  Tipo que representa los dominios de los símbolos
  de función de la signatura S.
-}
Dom : Signature → Set _
Dom S = NProd (sorts S)

{-
  Tipo que representa las aridades de los símbolos
  de función de la signatura S.
-}
Arity : Signature → Set _
Arity S = Dom S × (sorts S)

{-
  Dado un símbolo de función en la signatura S,
  retorna su dominio.
-}
fdom : ∀ {S : Signature} → (f : funcs S) → Dom S
fdom {S} f = proj₁ (arity S f)

{-
  Dado un símbolo de función en la signatura S,
  retorna su codominio.
-}
ftgt : ∀ {S : Signature} → (f : funcs S) → sorts S
ftgt {S} f = proj₂ (arity S f)


{-
  Tipo que representa la interpretación de un sort de
  la signatura S.
-}
ISorts : ∀ {l} → Signature → Set l → Set _
ISorts S A = (sorts S) → A


{- 
   Tipo que representa la interpretación de un dominio.
   Dado el dominio de un símbolo de función de la signatura S,
   retorna el tipo resultante de interpretar cada sort en el dominio.
-}
IDom : ∀ {S : Signature} {l} → Dom S → (ISorts S (Set l)) → Set _
IDom (zero , lift unit) i = Lift Unit
IDom (suc zero , a) i = i a
IDom {S} (suc (suc n) , (args , s)) i = IDom {S} (suc n , args) i × i s

{-
  Dada la aridad de un símbolo de función f en la signatura S, y 
  una función de interpretación de los sorts de S, retorna
  el tipo de la interpretación de la función f. 
-}
IFun : ∀ {S : Signature} {l} → Arity S → ((sorts S) → Set l) → Set l
IFun {S} (nargs , a) i = IDom {S} nargs i → i a


-- Algebra de una signatura S

record Algebra {l₁ l₂ : Level} (S : Signature) : 
                             Set (lsuc (l₁ ⊔ l₂)) where
  field
    isorts   : (s : sorts S) → Setoid l₁ l₂
    ifuns    : (f : funcs S) →
               IFun {S} (arity S f) (Carrier ∘ isorts)

open Algebra


{-
  Dado un símbolo de función f de la signatura S y un álgebra A de S,
  retorna el dominio de la interpretación de f.
-}
idom : ∀ {S} {l₁} {l₂} → (f : funcs S) → (A : Algebra {l₁} {l₂} S) → Set _ 
idom {S} f A = IDom {S} (fdom {S} f) (Carrier ∘ isorts A)

{-
  Dado un símbolo de función f de la signatura S y un álgebra A de S,
  retorna el codominio de la interpretación de f.
-}
itgt : ∀ {S} {l₁} {l₂} → (f : funcs S) → (A : Algebra {l₁} {l₂} S) → Set _ 
itgt {S} f A = Carrier $ isorts A (ftgt {S} f)


-- Función many sorted entre dos álgebras
-- (Ver si este es el nombre más adecuado)
FunAlg : ∀ {S : Signature} {l₁} {l₂} →
           (A : Algebra {l₁} {l₂} S) → (A' : Algebra {l₁} {l₂} S) →
           Set _
FunAlg {S} A A' = (s : sorts S) → isorts A s ⟶ isorts A' s



map× : ∀ {l₁} {l₂} {B B' : Setoid l₁ l₂} {S : Signature}
         {i : (sorts S) → Setoid l₁ l₂} {i' : (sorts S) → Setoid l₁ l₂} →
         (nargs : Dom S) →
         (as : IDom {S} nargs (Carrier ∘ i)) → (m : (s : sorts S) → (i s) ⟶ (i' s)) →
         IDom {S} nargs (Carrier ∘ i')
map×(zero , lift unit) (lift unit) m = lift unit
map× {B = B} {B' = B'} (suc zero , a) ia m = m a ⟨$⟩ ia
map× {B = B} {B' = B'} (suc (suc n) , args , a) (iargs , ia) m =
                              map× {B = B} {B' = B'}
                                   (suc n , args) iargs m , m a ⟨$⟩ ia



mapMorph : ∀ {S : Signature} {l₁} {l₂}
                {A A' : Algebra {l₁} {l₂} S}
                {f : funcs S} →
                (m : FunAlg A A') → (as : idom f A) → 
                idom f A'
mapMorph {S} {l₁} {l₂} {A} {A'} {f} m as =
                    map× {B = isorts A (ftgt {S} f)}
                         {B' = isorts A' (ftgt {S} f)}
                         (fdom {S} f) as m

{- 
   Definición de la propiedad de preservación de igualdad
   en el Homomorfismo entre A y A'.
-}
homPreserv : ∀ {l₁ l₂} → (S : Signature) → (A : Algebra {l₁} {l₂} S) →
                         (A' : Algebra {l₁} {l₂} S) →
                         FunAlg A A' →
                         (f : funcs S) → Set (l₂ ⊔ l₁)
homPreserv S A A' m f = (as : idom f A) →
                        _≈_ (isorts A' tgtf)
                            (m tgtf ⟨$⟩ (ifuns A f as))
                            (ifuns A' f (map× {B = (isorts A tgtf)}
                                              {B' = (isorts A' tgtf)}
                                              targs as m))
  where tgtf = ftgt {S} f
        targs = fdom {S} f

--Homomorfismo.

record Homomorphism {l₁ l₂ : Level} 
                    (S : Signature) (A A' : Algebra {l₁} {l₂} S) : 
                                    Set (lsuc (l₁ ⊔ l₂)) where
  field
    -- Familia de funciones
    morph  : FunAlg A A'
    -- Propiedad de preservación de operaciones.
    preserv : (f : funcs S) → homPreserv S A A' morph f


-- -- Igualdad de homomorfismos

open Homomorphism

data _≈ₕ_ {l₁ l₂} {S} {A A' : Algebra {l₁} {l₂} S} : 
          (H H' : Homomorphism S A A') → Set (lsuc (l₁ ⊔ l₂)) where
  ext : (H H' : Homomorphism S A A') → ((s : sorts S) → (a b : Carrier (isorts A s)) →
        _≈_ (isorts A s) a b → _≈_ (isorts A' s) (morph H s ⟨$⟩ a) (morph H' s ⟨$⟩ b)) →
        H ≈ₕ H'

≡to≈ : ∀ {l₁} {l₂} {St : Setoid l₁ l₂} {x y : Carrier St} →
       x ≡ y → _≈_ St x y
≡to≈ {St = St} PE.refl = Setoid.refl St
 

propMap×Comp : ∀ {l₁} {l₂} {B₀ B₁ B₂ : Setoid l₁ l₂} {S : Signature}
                 {i₀ : (sorts S) → Setoid l₁ l₂} {i₁ : (sorts S) → Setoid l₁ l₂}
                 {i₂ : (sorts S) → Setoid l₁ l₂} →
                 (nargs : Dom S) →
                 (as : IDom {S} nargs (Carrier ∘ i₀)) →
                 (m : (s : sorts S) → (i₀ s) ⟶ (i₁ s)) →
                 (m' : (s : sorts S) → (i₁ s) ⟶ (i₂ s)) →
                 (s : sorts S) →
                 map× {B = B₁} {B' = B₂} nargs (map× {B = B₀} {B' = B₁} nargs as m) m'
                 ≡
                 map× {B = B₀} {B' = B₂} nargs as (λ s' → m' s' ∘ₛ m s')
propMap×Comp (zero , lift unit) (lift unit) m m' s = _≡_.refl
propMap×Comp (suc zero , a) ia m m' s = _≡_.refl
propMap×Comp {B₀ = B₀} {B₁ = B₁} {B₂ = B₂}
             (suc (suc n) , args , a) (ias , ia) m m' s =
                          cong₂ (λ x y → x , y)
                                (propMap×Comp {B₀ = B₀} {B₁ = B₁} {B₂ = B₂}
                                              ((suc n) , args) ias m m' s)
                                              PE.refl



-- Composición de homomorfismos

{- Si H₀ : A₀ → A₁ y H₁ : A₁ → A₂, ambos preservan igualdad, 
      entonces la composición también -}

_∘ₕ_ : ∀ {l₁ l₂} {S} {A₀ A₁ A₂ : Algebra {l₁} {l₂} S} →
       (H₁ : Homomorphism S A₁ A₂) → (H₀ : Homomorphism S A₀ A₁) →
       Homomorphism S A₀ A₂
_∘ₕ_ {l₁} {l₂} {S} {A₀} {A₁} {A₂} H₁ H₀ =
               record { morph = comp
                      ; preserv = pres }
  where comp = λ s → morph H₁ s ∘ₛ morph H₀ s
        pres : (f : funcs S) → homPreserv S A₀ A₂ comp f
        pres f as = Setoid.trans (isorts A₂ s) (Π.cong (morph H₁ s) (p₀ as))
                    (Setoid.trans (isorts A₂ s) (p₁ (mapMorph {A = A₀} {A' = A₁}
                                                                 (morph H₀) as))
                                                propMapMorph)
          where p₁ = preserv H₁ f
                p₀ = preserv H₀ f
                s = ftgt {S} f
                args = fdom {S} f
                propMapMorph : _≈_ (isorts A₂ s)
                               ((ifuns A₂ f) (mapMorph {A = A₁} {A' = A₂}
                                                       (morph H₁)
                                                   (mapMorph {A = A₀} {A' = A₁}
                                                                (morph H₀) as)))
                               ((ifuns A₂ f) (mapMorph {A = A₀} {A' = A₂}
                                                       comp as))
                propMapMorph = ≡to≈ {St = isorts A₂ s} (PE.cong (ifuns A₂ f)
                               (propMap×Comp args as (morph H₀) (morph H₁) s))

{-
                 Esta seria la prueba pres en un lenguaje mas ameno:

                 p₀ :   H₀ fₐ₀ as ≈ₐ₁ fₐ₁ (map× H₀ as)

                 p₁ :   H₁ fₐ₁ as ≈ₐ₂ fₐ₂ (map× H₁ as)


                    Hₒ fₐ₀ as ≈ₐ₂ fₐ₂ (map× Hₒ as)

                   si Hᵢ es una funcion que preserva igualdad, entonces:

                   H₁ (H₀ fₐ₀ as) ≈ₐ₁ H₁ (fₐ₁ (map× H₀ as)) (por p₀ y cong)

                   luego H₁ (fₐ₁ (map× H₀ as)) ≈ₐ₂ fₐ₂ (map× H₁ (map× H₀ as)) 
                   
                   (y luego deberíamos ver que map× H₁ ∘ map× H₀ ≡ map× Hₒ y esto
                    se prueba en map×CompProp

 -}
