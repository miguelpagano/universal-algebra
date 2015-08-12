module UnivAlgebra where

open import Relation.Binary
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Nat hiding (_⊔_)
open import Data.Vec hiding (init)
open import Data.Product hiding (map)
open import Function
open import Function.Equality renaming (_∘_ to _∘ₛ_)
open import Data.Unit hiding (setoid)
open import Data.Bool
open import Relation.Binary.PropositionalEquality as PE
open import Induction.WellFounded


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

sizeDom : ∀ {S : Signature} → (f : funcs S) → ℕ
sizeDom {S} = proj₁ ∘ fdom {S}


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



map× : ∀ {l₁} {B B' : Set l₁} {S : Signature}
         {i : (sorts S) → Set l₁} {i' : (sorts S) → Set l₁} →
         (nargs : Dom S) →
         (as : IDom {S} nargs i) → (m : (s : sorts S) → (i s) → (i' s)) →
         IDom {S} nargs i'
map×(zero , lift unit) (lift unit) m = lift unit
map× {B = B} {B' = B'} (suc zero , a) ia m = m a ia
map× {B = B} {B' = B'} (suc (suc n) , args , a) (iargs , ia) m =
                              map× {B = B} {B' = B'}
                                   (suc n , args) iargs m , m a ia



mapMorph : ∀ {S : Signature} {l₁} {l₂}
                {A A' : Algebra {l₁} {l₂} S}
                {f : funcs S} →
                (m : FunAlg A A') → (as : idom f A) → 
                idom f A'
mapMorph {S} {l₁} {l₂} {A} {A'} {f} m as =
                    map× {B = Carrier $ isorts A (ftgt {S} f)}
                         {B' = Carrier $ isorts A' (ftgt {S} f)}
                         (fdom {S} f) as (λ s → _⟨$⟩_ (m s))

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
                            (ifuns A' f (mapMorph {S} {A = A} {A' = A'} {f = f}
                                                  m as))
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
 

propMap×Comp : ∀ {l₁} {B₀ B₁ B₂ : Set l₁} {S : Signature}
                 {i₀ : (sorts S) → Set l₁} {i₁ : (sorts S) → Set l₁}
                 {i₂ : (sorts S) → Set l₁} →
                 (nargs : Dom S) →
                 (as : IDom {S} nargs i₀) →
                 (m : (s : sorts S) → (i₀ s) → (i₁ s)) →
                 (m' : (s : sorts S) → (i₁ s) → (i₂ s)) →
                 (s : sorts S) →
                 map× {B = B₁} {B' = B₂} nargs (map× {B = B₀} {B' = B₁} nargs as m) m'
                 ≡
                 map× {B = B₀} {B' = B₂} nargs as (λ s' → m' s' ∘ m s')
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
                               (propMap×Comp args as (λ s' → _⟨$⟩_ (morph H₀ s'))
                                                     (λ s' → _⟨$⟩_ (morph H₁ s')) s))

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


Unicity : ∀ {l₁} {l₂} → (A : Set l₁) → (A → A → Set l₂) → Set _ 
Unicity A rel = Σ A (λ a → (a' : A) → rel a a')


record Initial {l₁ l₂ : Level} (S : Signature) : 
                             Set (lsuc (l₁ ⊔ l₂)) where
  field
    alg      : Algebra {l₁} {l₂} S
    init     : (A : Algebra {l₁} {l₂} S) → Unicity (Homomorphism S alg A) (_≈ₕ_)


-- Algebra de términos

-- Carriers del álgebra de términos de una signatura
data HerbrandUniverse (S : Signature) : (s : sorts S) → Set where
  term    : (f : funcs S) →
            (ts : IDom {S} (fdom {S} f) (HerbrandUniverse S)) →
            HerbrandUniverse S (ftgt {S} f)



data _∈ₜ_ : ∀ {S} {fsig : Dom S}  → {B : Set} → 
              B → IDom {S} fsig (HerbrandUniverse S) → Set₁ where 
     empty∈ : ∀ {S} {ids : IDom {S} (zero , lift unit) (HerbrandUniverse S)} → 
              _∈ₜ_ {S} {(zero , lift unit)} {Lift Unit} (lift unit) ids
     unary∈ : ∀ {S} {s : sorts S} {t : HerbrandUniverse S s}
              {ids : IDom {S} (suc zero , s) (HerbrandUniverse S)} → 
              _∈ₜ_ {S} {(suc zero , s)} {HerbrandUniverse S s} t ids
     here∈  : ∀ {S} {n} {args} {s : sorts S} {t : HerbrandUniverse S s}
              {ids : IDom {S} (suc (suc n) , (args , s)) (HerbrandUniverse S)} → 
              _∈ₜ_ {S} {(suc (suc n) , (args , s))} {HerbrandUniverse S s}
                   t ids
     there∈ :  ∀ {S} {n} {args} {s : sorts S} {s' : sorts S}
               {t : HerbrandUniverse S s} {t' : HerbrandUniverse S s'}
               {ids : IDom {S} (suc n , args) (HerbrandUniverse S)} → 
               _∈ₜ_ {S} {(suc n , args)} {HerbrandUniverse S s} t ids →
               _∈ₜ_ {S} {(suc (suc n) , args , s')} {HerbrandUniverse S s} t (ids , t')
     

-- Relacion de orden entre Herbrand...

data _<ₜ_ {S : Signature} : ∀ {s s'} → HerbrandUniverse S s →
                                       HerbrandUniverse S s' → Set₁ where
     tless : ∀ {s : sorts S} {s' : sorts S} {f : funcs S}
               {t : HerbrandUniverse S s} {ts : IDom {S} (fdom {S} f) (HerbrandUniverse S)} →
               _∈ₜ_ {S} {fdom {S} f} {HerbrandUniverse S s} t ts →
               t <ₜ term f ts

-- TODO: Pensar los niveles.

l₁ : Level
l₁ = lsuc lzero

-- Relación sobre un tipo indizado
HRel : ∀ {B : Set} → (A : B → Set) → (b : B) → (b' : B) → Set _
HRel A b b' = REL (A b) (A b') l₁

data Acc' {B : Set} {A : B → Set} {b̃} (rel : ∀ {b b'} → HRel A b b') (x : A b̃) : Set l₁ where
  acc' :  (∀ {b₀} → ∀ y → rel {b₀} {b̃} y x → Acc' {B} {A} {b₀} rel y) → Acc' rel x

WellFounded : ∀ {B : Set} {A : B → Set} → (∀ {b b'} → HRel A b b') → Set _
WellFounded {B} {A} rel = ∀ {b : B} → (x : A b) → Acc' {B} {A} {b} rel x

foldAcc' : ∀ {B : Set} {A : B → Set}  {rel : (∀ {b b'} → HRel A b b')}
             (P : ∀ {b} → A b → Set) →
             (∀ {b'} x → (∀ {b} y → rel {b} {b'} y x → P y) → P x) →
             ∀ {b̃} z → Acc' {B} {A} {b̃} rel z → P z
foldAcc' P ind z (acc' a) = ind z (λ y rel_y_z → foldAcc' P ind y (a y rel_y_z))

-- Recursion para HRels bien fundadas
rec : ∀ {B : Set} {A : B → Set}  {rel : (∀ {b b'} → HRel A b b')} →
        WellFounded {B} {A} rel → (P : ∀ {b} → A b → Set) →
        (∀ {b'} x → (∀ {b} y → rel {b} {b'} y x → P y) → P x) →
        ∀ {b̃}z  → P {b̃} z
rec wf P ind z = foldAcc' P ind z (wf z)

-- _<ₜ_ es bien fundada
well-founded<ₜ : ∀ {S : Signature} → WellFounded {sorts S} {HerbrandUniverse S} (_<ₜ_ {S})
well-founded<ₜ {S} (term f ts) = acc' acc<ₜ
  where acc<ₜ : ∀ {s₀} → ∀ y → _<ₜ_ {S} {s₀} {ftgt {S} f} y (term f ts) → Acc' {sorts S} {HerbrandUniverse S} {s₀} _<ₜ_ y
        acc<ₜ t' (tless x) = {!!}

termAlgebra : (S : Signature) → Algebra {lzero} {lzero} S
termAlgebra S = record { isorts = λ s → PE.setoid (HerbrandUniverse S s)
                       ; ifuns = λ f t → term f t }


{-
-- Homomorfismo del álgebra de términos a cualquier otra álgebra
tAlgHomo : ∀ {S} → (A : Algebra {lzero} {lzero} S) → Homomorphism S (termAlgebra S) A
tAlgHomo {S} A = record { morph = λ s → record { _⟨$⟩_ = fun s
                                               ; cong = {!!} }
                    ; preserv = {!!} }
  where fun : (s : sorts S) → HerbrandUniverse S s → Carrier (isorts A s)
        fun = {!!}
        {- fun ._ (term f t) = ifuns A f (map× {B = HerbrandUniverse S (ftgt {S} f)}
                                            {B' = Carrier $ isorts A (ftgt {S} f)}
                                            {S = S}
                                            (fdom {S} f) t {!!} )--fun) -}


{-
-- El álgebra de términos es inicial
tAlgInit : (S : Signature) → Initial {lzero} {lzero} S
tAlgInit S = record { alg = termAlgebra S
                    ; init = tinit }
  where tinit : (A : Algebra {lzero} {lzero} S) →
                Unicity (Homomorphism S (termAlgebra S) A) (_≈ₕ_)
        tinit A = tAlgHomo A , uni
          where uni : (h : Homomorphism S (termAlgebra S) A) → tAlgHomo A ≈ₕ h
                uni h = {!!}

-}
-}
