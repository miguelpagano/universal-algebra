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
open import Data.List
open import Relation.Binary.PropositionalEquality as PE
open import Induction.WellFounded

open Setoid


record Signature : Set₁ where
  field
    sorts  : Set
    funcs  : List sorts × sorts → Set


open Signature

Arity : (S : Signature) → Set
Arity S = List (sorts S)

SType : (S : Signature) → Set
SType S = Arity S × (sorts S)



{-
  Tipo que representa la interpretación de un sort de
  la signatura S.
-}
ISorts : ∀ {l} → Signature → Set l → Set _
ISorts S A = (sorts S) → A


{- 
   Tipo que representa la interpretación de la aridad de una función.
   Dada la aridad de un símbolo de función de la signatura S,
   retorna el tipo resultante de interpretar cada sort en la aridad.
-}
IDom : ∀ {l} → (S : Signature) → Arity S → (ISorts S (Set l)) → Set _
IDom S [] i = Lift Unit
IDom S (s ∷ []) i = i s
IDom S (s₀ ∷ rest) i = i s₀ × IDom S rest i

{-
  Dada la aridad de un símbolo de función f en la signatura S, el sort
  target y una función de interpretación de los sorts de S, retorna
  el tipo de la interpretación de la función f. 
-}
IFun : ∀ {l} → (S : Signature) → (ty : SType S) →
               ISorts S (Set l)  → Set l
IFun S (ar , s) i = IDom S ar i → i s


-- Algebra de una signatura S
record Algebra {l₁ l₂ : Level} (S : Signature) : 
                             Set (lsuc (l₁ ⊔ l₂)) where
  field
    isorts   : (s : sorts S) → Setoid l₁ l₂
    ifuns    : (ty : SType S) → (f : funcs S ty) → IFun S ty (Carrier ∘ isorts)

open Algebra

idom : ∀ {S} {l₁} {l₂} → (ty : SType S) → (A : Algebra {l₁} {l₂} S) → Set _ 
idom {S} (ar , _) A = IDom S ar (Carrier ∘ isorts A)

-- Función many sorted entre dos álgebras
-- (Ver si este es el nombre más adecuado)
FunAlg : ∀ {S : Signature} {l₁} {l₂} →
           (A : Algebra {l₁} {l₂} S) → (A' : Algebra {l₁} {l₂} S) →
           Set _
FunAlg {S} A A' = (s : sorts S) → isorts A s ⟶ isorts A' s

map× : ∀ {l₁} {S : Signature}
         {i : (sorts S) → Set l₁} {i' : (sorts S) → Set l₁} →
         (arty : Arity S) →
         (as : IDom S arty i) → (m : (s : sorts S) → (i s) → (i' s)) →
         IDom S arty i'
map× [] (lift unit) m = lift unit
map× (s ∷ []) is m = m s is
map× (s₀ ∷ s₁ ∷ rest) (is₀ , irest) m = m s₀ is₀ , map× (s₁ ∷ rest) irest m


mapMorph : ∀ {S : Signature} {l₁} {l₂}
                {A A' : Algebra {l₁} {l₂} S}
                {ty : SType S}
                (m : FunAlg A A') → (as : idom ty A) → 
                idom ty A'
mapMorph {S} {_} {_} {A} {A'} {ty = ar , s} m as = map× ar as (λ s → _⟨$⟩_ (m s))

{- 
   Definición de la propiedad de preservación de igualdad
   en el Homomorfismo entre A y A'.
-}
homPreserv : ∀ {l₁ l₂} → (S : Signature) → (A : Algebra {l₁} {l₂} S) →
                         (A' : Algebra {l₁} {l₂} S) →
                         FunAlg A A' → (ty : SType S) →
                         (f : funcs S ty) → Set (l₂ ⊔ l₁)
homPreserv S A A' m (ar , s) f =
                        (as : idom (ar , s) A) →
                        _≈_ (isorts A' s)
                            (m s ⟨$⟩ (ifuns A (ar , s) f as))
                            (ifuns A' (ar , s) f (mapMorph {S} {A = A} {A' = A'} {ty = (ar , s)}
                                                  m as))

--Homomorfismo.

record Homomorphism {l₁ l₂ : Level} 
                    (S : Signature) (A A' : Algebra {l₁} {l₂} S) : 
                                    Set (lsuc (l₁ ⊔ l₂)) where
  field
    -- Familia de funciones
    morph  : FunAlg A A'
    -- Propiedad de preservación de operaciones.
    preserv : (ty : SType S) → (f : funcs S ty) → homPreserv S A A' morph ty f

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


propMap×Comp : ∀ {l₁} {S : Signature}
                 {i₀ : (sorts S) → Set l₁} {i₁ : (sorts S) → Set l₁}
                 {i₂ : (sorts S) → Set l₁} →
                 (ar : Arity S) →
                 (d : IDom S ar i₀) →
                 (m : (s : sorts S) → (i₀ s) → (i₁ s)) →
                 (m' : (s : sorts S) → (i₁ s) → (i₂ s)) →
                 map× ar (map× ar d m) m'
                 ≡
                 map× ar d (λ s' → m' s' ∘ m s')
propMap×Comp [] (lift unit) m m' = PE.refl
propMap×Comp (s ∷ []) d m m' = PE.refl
propMap×Comp (s₀ ∷ s₁ ∷ rest) (is₀ , irest) m m' =
                   cong₂ (λ x y → x , y) PE.refl
                         (propMap×Comp (s₁ ∷ rest) irest m m')

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
        pres :  (ty : SType S) → (f : funcs S ty) → homPreserv S A₀ A₂ comp ty f
        pres (ar , s) f as = Setoid.trans (isorts A₂ s) (Π.cong (morph H₁ s) (p₀ as))
                    (Setoid.trans (isorts A₂ s) (p₁ (mapMorph {A = A₀} {A' = A₁} {ty = ty}
                                                                 (morph H₀) as))
                                                propMapMorph)
          where ty = (ar , s)
                p₁ = preserv H₁ (ar , s) f
                p₀ = preserv H₀ (ar , s) f
                propMapMorph : _≈_ (isorts A₂ s)
                               ((ifuns A₂ ty f) (mapMorph {A = A₁} {A' = A₂} {ty = ty}
                                                       (morph H₁)
                                                   (mapMorph {A = A₀} {A' = A₁} {ty = ty}
                                                                (morph H₀) as)))
                               ((ifuns A₂ ty f) (mapMorph {A = A₀} {A' = A₂} {ty = ty}
                                                       comp as))
                propMapMorph = ≡to≈ {St = isorts A₂ s} (PE.cong (ifuns A₂ ty f)
                               (propMap×Comp ar as (λ s' → _⟨$⟩_ (morph H₀ s'))
                                                     (λ s' → _⟨$⟩_ (morph H₁ s'))))


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

{-
-- Algebra de términos


-- Carriers del álgebra de términos de una signatura. Lo defino solo para
-- sorts alcanzables.
data HerbrandUniverse (S : Signature) : (s : sorts S) → Set where
  consT : (c : consts S) → HerbrandUniverse S (consTy S c)
  funT  : (f : funcs S) →
          (ts : IDom {S} (arity {S} f) (HerbrandUniverse S)) →
          HerbrandUniverse S (ftgt {S} f)


HU : (S : Signature) → (s : sorts S) → Set
HU = HerbrandUniverse

data _∈ₜ_ : ∀ {S : Signature} {farty : Arityₛ S} {s : sorts S} → 
              HerbrandUniverse S s → IDom {S} farty (HerbrandUniverse S) → Set₁ where 
     unary∈ : ∀ {S} {s : sorts S} {t : HerbrandUniverse S s} → 
              _∈ₜ_ {S} {naryA {n = zero} s} t t
     here∈  : ∀ {S} {n} {sargs} {s : sorts S} {t : HerbrandUniverse S s}
              {ids : IDom {S} (naryA {n = n} sargs) (HerbrandUniverse S)} → 
              _∈ₜ_ {S} {naryA {n = suc n} (sargs , s)}
                   t (ids , t)
     there∈ :  ∀ {S} {n} {sargs} {s : sorts S} {s' : sorts S}
               {t : HerbrandUniverse S s} {t' : HerbrandUniverse S s'}
               {ids : IDom {S} (naryA {n = n} sargs) (HerbrandUniverse S)} → 
               _∈ₜ_ {S} {naryA {n = n} sargs} t ids →
               _∈ₜ_ {S} {naryA {n = suc n} (sargs , s')} t (ids , t')

-- Relacion de orden entre Herbrand...
data _<ₜ_ {S : Signature} : ∀ {s s'} → HerbrandUniverse S s →
                                        HerbrandUniverse S s' → Set₁ where
     lessₜ    : ∀  {s : sorts S} {f : funcs S} {t : HerbrandUniverse S s} {ts} →
                  _∈ₜ_ {S} {arity {S} f} t ts →
                  _<ₜ_ {s = s} {s' = ftgt {S} f} t (funT f ts)

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

acc<ₜ : ∀ {S} (f : funcs S) → (ts : IDom {S} (arity {S} f) (HU S)) →
              {s₀ : sorts S} → (t₀ : HU S s₀) → 
              _<ₜ_ {S} {s₀} {ftgt {S} f} t₀ (funT f ts) →
                Acc' {sorts S} {HerbrandUniverse S} {s₀} _<ₜ_ t₀
acc<ₜ {S} f ts {s₀} t₀ (lessₜ {.s₀} {ts = .ts} x) with arity {S} f
acc<ₜ f ts (consT c) (lessₜ _) | naryA x = acc' λ _ → λ ()
acc<ₜ f .(funT f₁ ts₁) (funT f₁ ts₁) (lessₜ unary∈) | naryA ._ =
      acc' (λ t₀ t₀<ₜt → acc<ₜ f₁ ts₁ t₀ t₀<ₜt)
acc<ₜ f ._ (funT f₁ ts₁) (lessₜ here∈) | naryA ._ =
      acc' (λ t₀ t₀<ₜt → acc<ₜ f₁ ts₁ t₀ t₀<ₜt)
acc<ₜ f ._ (funT f₁ ts₁) (lessₜ (there∈ x₁)) | naryA ._ =
      acc' (λ t₀ t₀<ₜt → {!!})



{-acc<ₜ {S} f (consT c) .(consT c) (lessₜ unary∈) | naryA {zero} ._ = acc' λ _ ()
acc<ₜ f (funT f₁ ts) .(funT f₁ ts) (lessₜ unary∈) | naryA {zero} ._ =
      acc' (λ t₀ t₀<ₜt → acc<ₜ f₁ ts t₀ t₀<ₜt)
-}
well-founded<ₜ : ∀ {S} → WellFounded {sorts S} {HerbrandUniverse S} (_<ₜ_ {S})
well-founded<ₜ {S} (consT c) = acc' λ _ ()
well-founded<ₜ (funT f ts) = acc' (acc<ₜ f ts)

{-
  where consAcc : ∀ {s₀} → (t₀ : HU S s₀) → t₀ <ₜ (consT x) → Acc' {sorts (sign S)} {HU S} _<ₜ_ t₀
        consAcc t₀ ()
well-founded<ₜ (funT x ts) = {!!}

acc<ₜ {S} s₀ t₀ f ts (lessₜ {.s₀} {ts = .ts} x) with fdom {sign S} f
acc<ₜ s₀ t₀ f ts (lessₜ ()) | zeroA
acc<ₜ s₀ t₀ f ts (lessₜ x₁) | naryA {zero} x = {!!}
acc<ₜ s₀ t₀ f ts (lessₜ x₁) | naryA {suc n} x = {!!}

acc<ₜ {S} s₀ t₀ f ts (tless {.s₀} {ts = .ts} t₀<ₜt) with fdom {S} f
acc<ₜ s₀ t₀ f ts (tless ()) | zero , proj₂
acc<ₜ {S} s₀ t₀ f ts (tless t₀<ₜt) | suc zero , proj₂ = {!!}
  where acc₁ : ∀ {s : sorts S} → (t‼ : HU S s) → t‼ <ₜ t₀ → Acc' {sorts S} {HU S} {s} _<ₜ_ t‼
        acc₁ t‼ tl = {!!}
acc<ₜ s₀ t₀ f ts (tless t₀<ₜt) | suc (suc proj₁) , proj₂ = {!!}



well-founded<ₜ : ∀ {S : Signature} → WellFounded {sorts S} {HerbrandUniverse S} (_<ₜ_ {S})
well-founded<ₜ {S} (term f ts) = {!!} -- acc' (λ {s₀} → acc<ₜ s₀)
{-  where acc<ₜ : ∀ s₀ t₀ f ts' → _<ₜ_ {S} {s₀} {ftgt {S} f'} t₀ (term f' ts') → Acc' {sorts S} {HerbrandUniverse S} {s₀} _<ₜ_ t'
        acc<ₜ s₀ f' ts' t' (tless {.s₀} {ts = .ts'} t'<ₜt) with fdom {S} f'
        acc<ₜ s₀ f' _ t' (tless ()) | zero , lift unit
        acc<ₜ ._ f' t₀ (term f₁ ts₁) (tless t'<ₜt) | suc zero , proj₂ = {!!}
        acc<ₜ s₀ f' ts' t' (tless lt) | suc (suc proj₁) , proj₂ = {!!}-}

        acc<ₜ s₀ g (lift unit) t' (tless lt) | (zero , lift unit) , s' = {!!}
        acc<ₜ s₀ g as t' (tless lt) | (suc zero , s) , s' = {!lt!}
        acc<ₜ s₀ g (a , as) t' (tless lt) | (suc (suc n) , s₁ , sn) , s' = {!!} -}

termAlgebra : (S : Signature) → Algebra {lzero} {lzero} S
termAlgebra S = record { isorts = λ s → PE.setoid (HU S s)
                       ; icons = λ c → consT c
                       ; ifuns = λ f ts → funT f ts }

-- Homomorfismo del álgebra de términos a cualquier otra álgebra
tAlgHomo : ∀ {S} → (A : Algebra {lzero} {lzero} S) → Homomorphism S (termAlgebra S) A
tAlgHomo {S} A = record { morph = λ s → record { _⟨$⟩_ = fun s
                                               ; cong = {!!} }
                        ; conspreserv = {!!}
                        ; funpreserv = {!!} }
  where fun : (s : sorts S) → HerbrandUniverse S s → Carrier (isorts A s)
        fun ._ (consT c) = icons A c
        fun ._ (funT f ts) with arity {S} f
        fun ._ (funT f t) | naryA {zero} s = ifuns A f {!f!}
        fun ._ (funT f ts) | naryA {suc n} x = {!!}
                              {- ifuns A f (map× {B = HerbrandUniverse S (ftgt {S} f)}
                                            {B' = Carrier $ isorts A (ftgt {S} f)}
                                            (arity {S} f) ts fun) -}
{-

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
-}
