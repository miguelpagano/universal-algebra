module UnivAlgebra where

open import Relation.Binary
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Nat renaming (_⊔_ to _⊔ₙ_)
open import Data.Product renaming (map to pmap)
open import Function
open import Function.Equality renaming (_∘_ to _∘ₛ_)
open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality as PE
open import Induction.WellFounded
open import Data.String
open import Data.Fin
open import VecH

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
  Dada una familia I indexada en los sorts de S,
  interpretar un simbolo de funcion con aridad ar y tipo de retorno s,
  es una funcion que va de un vector heterogéneo con interpretación I y
  aridad ar en I s.
-}
IFun : ∀ {l} → (S : Signature) → (ty : SType S) →
               ISorts S (Set l)  → Set l
IFun S (ar , s) I = VecH (sorts S) I ar → I s


-- Algebra de una signatura S
record Algebra {l₁ l₂ : Level} (S : Signature) : 
                             Set (lsuc (l₁ ⊔ l₂)) where
  field
    isorts   : (s : sorts S) → Setoid l₁ l₂
    ifuns    : (ty : SType S) → (f : funcs S ty) → IFun S ty (Carrier ∘ isorts)
    ifuncong : ∀ {ar} {s} {f} →
               (ts₁ ts₂ : VecH (sorts S) (Carrier ∘ isorts) ar) →
               _∼v_ {R = _≈_ ∘ isorts} ts₁ ts₂ →
               _≈_ (isorts s) (ifuns (ar , s) f ts₁)
                              (ifuns (ar , s) f ts₂)

open Algebra

idom : ∀ {S} {l₁} {l₂} → (ar : Arity S) → (A : Algebra {l₁} {l₂} S) → Set _ 
idom {S} ar A = VecH (sorts S) (Carrier ∘ isorts A) ar

-- Función many sorted entre dos álgebras
FunAlg : ∀ {S : Signature} {l₁} {l₂} {l₃} {l₄} →
           (A : Algebra {l₁} {l₂} S) → (A' : Algebra {l₃} {l₄} S) →
           Set _
FunAlg {S} A A' = (s : sorts S) → isorts A s ⟶ isorts A' s


mapMorph : ∀ {S : Signature} {l₁} {l₂} {l₃} {l₄}
                {A : Algebra {l₁} {l₂} S} {A' : Algebra {l₃} {l₄} S}
                {ar : Arity S}
                (m : FunAlg A A') → (ts : idom ar A) → 
                idom ar A'
mapMorph {ar = ar} m ts = mapV (_⟨$⟩_ ∘ m) ar ts

{- 
   Definición de la propiedad de preservación de igualdad
   en el Homomorfismo entre A y A'.
-}
homPreserv : ∀ {l₁ l₂ l₃ l₄} → (S : Signature) → (A : Algebra {l₁} {l₂} S) →
                         (A' : Algebra {l₃} {l₄} S) →
                         FunAlg A A' → (ty : SType S) →
                         (f : funcs S ty) → Set _
homPreserv S A A' m (ar , s) f =
                        (as : idom ar A) →
                        _≈_ (isorts A' s)
                            (m s ⟨$⟩ (ifuns A (ar , s) f as))
                            (ifuns A' (ar , s) f (mapMorph {S} {A = A} {A' = A'} {ar = ar}
                                                  m as))


--Homomorfismo.

record Homomorphism {l₁ l₂ l₃ l₄} (S : Signature)
                    (A : Algebra {l₁} {l₂} S) (A' : Algebra {l₃} {l₄} S) : 
                                    Set (lsuc (l₄ ⊔ l₃ ⊔ l₁ ⊔ l₂)) where
  field
    -- Familia de funciones
    morph  : FunAlg A A'
    -- Propiedad de preservación de operaciones.
    preserv : (ty : SType S) → (f : funcs S ty) → homPreserv S A A' morph ty f

open Homomorphism

-- -- Igualdad de homomorfismos
data _≈ₕ_ {l₁ l₂ l₃ l₄} {S} {A : Algebra {l₁} {l₂} S} {A' : Algebra {l₃} {l₄} S} : 
          (H H' : Homomorphism S A A') → Set (lsuc (l₄ ⊔ l₃ ⊔ l₁ ⊔ l₂)) where
  ext : (H H' : Homomorphism S A A') → ((s : sorts S) → (a b : Carrier (isorts A s)) →
        _≈_ (isorts A s) a b → _≈_ (isorts A' s) (morph H s ⟨$⟩ a) (morph H' s ⟨$⟩ b)) →
        H ≈ₕ H'

elim≈ₕ : ∀ {l₁ l₂ l₃ l₄} {S} {A : Algebra {l₁} {l₂} S} {A' : Algebra {l₃} {l₄} S} →
          {H H' : Homomorphism S A A'} → (H ≈ₕ H') →
          (s : sorts S) → (a b : Carrier (isorts A s)) → _≈_ (isorts A s) a b →
            _≈_ (isorts A' s) (morph H s ⟨$⟩ a) (morph H' s ⟨$⟩ b)
elim≈ₕ (ext H H' eq) s a b = eq s a b


≡to≈ : ∀ {l₁} {l₂} {St : Setoid l₁ l₂} {x y : Carrier St} →
       x ≡ y → _≈_ St x y
≡to≈ {St = St} PE.refl = Setoid.refl St



-- Composición de homomorfismos
_∘ₕ_ : ∀ {l₁ l₂ l₃ l₄ l₅ l₆} {S} {A₀ : Algebra {l₁} {l₂} S}
         {A₁ : Algebra {l₃} {l₄} S} {A₂ : Algebra {l₅} {l₆} S} →
       (H₁ : Homomorphism S A₁ A₂) → (H₀ : Homomorphism S A₀ A₁) →
       Homomorphism S A₀ A₂
_∘ₕ_ {S = S} {A₀} {A₁} {A₂} H₁ H₀ =
               record { morph = comp
                      ; preserv = pres }
  where comp = λ s → morph H₁ s ∘ₛ morph H₀ s
        pres :  (ty : SType S) → (f : funcs S ty) → homPreserv S A₀ A₂ comp ty f
        pres (ar , s) f as = Setoid.trans (isorts A₂ s) (Π.cong (morph H₁ s) (p₀ as))
                    (Setoid.trans (isorts A₂ s) (p₁ (mapMorph {A = A₀} {A' = A₁} {ar = ar}
                                                                 (morph H₀) as))
                                                propMapMorph)
          where ty = (ar , s)
                p₁ = preserv H₁ (ar , s) f
                p₀ = preserv H₀ (ar , s) f
                propMapMorph : _≈_ (isorts A₂ s)
                               ((ifuns A₂ ty f) (mapMorph {A = A₁} {A' = A₂} {ar = ar}
                                                       (morph H₁)
                                                   (mapMorph {A = A₀} {A' = A₁} {ar = ar}
                                                                (morph H₀) as)))
                               ((ifuns A₂ ty f) (mapMorph {A = A₀} {A' = A₂} {ar = ar}
                                                       comp as))
                propMapMorph = ≡to≈ {St = isorts A₂ s} (PE.cong (ifuns A₂ ty f)
                               (propMapVComp ar as (λ s' → _⟨$⟩_ (morph H₀ s'))
                                                   (λ s' → _⟨$⟩_ (morph H₁ s'))))

{-
                 Esta seria la prueba pres en un lenguaje mas ameno:

                 p₀ :   H₀ fₐ₀ as ≈ₐ₁ fₐ₁ (mapV H₀ as)

                 p₁ :   H₁ fₐ₁ as ≈ₐ₂ fₐ₂ (mapV H₁ as)


                    Hₒ fₐ₀ as ≈ₐ₂ fₐ₂ (mapV Hₒ as)

                   si Hᵢ es una funcion que preserva igualdad, entonces:

                   H₁ (H₀ fₐ₀ as) ≈ₐ₁ H₁ (fₐ₁ (mapV H₀ as)) (por p₀ y cong)

                   luego H₁ (fₐ₁ (mapV H₀ as)) ≈ₐ₂ fₐ₂ (mapV H₁ (mapV H₀ as)) 
                   
                   (y luego deberíamos ver que mapV H₁ ∘ mapV H₀ ≡ mapV Hₒ y esto
                    se prueba en mapVCompProp

 -}

-- Los homomorfismos forman un setoide respecto a la igualdad ≈ₕ.
hrefl : ∀ {l₁ l₂ l₃ l₄} {S} {A₁ : Algebra {l₁} {l₂} S} {A₂ : Algebra {l₃} {l₄} S} →
                          (H₁ : Homomorphism S A₁ A₂) → H₁ ≈ₕ H₁
hrefl {A₂ = A₂} H₁ = ext H₁ H₁ (λ s a b a=b → Π.cong (morph H₁ s) a=b)

hsym : ∀ {l₁ l₂ l₃ l₄} {S} {A₁ : Algebra {l₁} {l₂} S} {A₂ : Algebra {l₃} {l₄} S} →
                          (H₁ H₂ : Homomorphism S A₁ A₂) → H₁ ≈ₕ H₂ → H₂ ≈ₕ H₁
hsym {S = S} {A₁ = A₁} {A₂ = A₂} H₁ H₂ eq = ext H₂ H₁ equ
  where equ : (s : sorts S) → (a b : Carrier (isorts A₁ s)) →
              _≈_ (isorts A₁ s) a b →
              _≈_ (isorts A₂ s) (morph H₂ s ⟨$⟩ a) (morph H₁ s ⟨$⟩ b)
        equ s a b a=b = Setoid.sym (isorts A₂ s)
                               (elim≈ₕ eq s b a (Setoid.sym (isorts A₁ s) a=b))

htrans : ∀ {l₁ l₂ l₃ l₄} {S} {A₁ : Algebra {l₁} {l₂} S} {A₂ : Algebra {l₃} {l₄} S} →
                          (H₁ H₂ H₃ : Homomorphism S A₁ A₂) →
                           H₁ ≈ₕ H₂ → H₂ ≈ₕ H₃ → H₁ ≈ₕ H₃
htrans {S = S} {A₁ = A₁} {A₂ = A₂} H₁ H₂ H₃ eq eq' = ext H₁ H₃ equ
  where equ : (s : sorts S) → (a b : Carrier (isorts A₁ s)) →
              _≈_ (isorts A₁ s) a b → _
        equ s a b a=b = Setoid.trans (isorts A₂ s)
                                 (elim≈ₕ eq s a a (Setoid.refl (isorts A₁ s) {x = a}))
                                 (elim≈ₕ eq' s a b a=b)


-- Definición de unicidad
Unicity : ∀ {l₁} {l₂} → (A : Set l₁) → (A → A → Set l₂) → Set _ 
Unicity A rel = Σ A (λ a → (a' : A) → rel a a')


-- Álgebra inicial
record Initial {l₁ l₂ l₃ l₄ : Level} (S : Signature) : 
                             Set (lsuc (l₄ ⊔ l₃ ⊔ l₁ ⊔ l₂)) where
  field
    alg      : Algebra {l₁} {l₂} S
    init     : (A : Algebra {l₃} {l₄} S) → Unicity (Homomorphism S alg A) (_≈ₕ_)

  homInit : (A : Algebra S) → Homomorphism S alg A
  homInit A = proj₁ (init A)

  unique : (A : Algebra S) (h₁ h₂ : Homomorphism S alg A) → h₁ ≈ₕ h₂
  unique A h₁ h₂ = htrans h₁ (homInit A) h₂ h₁≈i i≈h₂
    where h₁≈i : _
          h₁≈i = hsym (homInit A) h₁ (proj₂ (init A) h₁)
          i≈h₂ : _
          i≈h₂ = proj₂ (init A) h₂

-- Algebra de términos


-- Carriers del álgebra de términos de una signatura. HU es por Herbrand Universe.
data HU (S : Signature) : (s : sorts S) → Set where
  term : ∀ {ar} {s} → (f : funcs S (ar , s)) →
                      (ts : VecH (sorts S) (HU S) ar) → HU S s

termAlgebra : (S : Signature) → Algebra {lzero} {lzero} S
termAlgebra S = record { isorts = PE.setoid ∘ HU S
                       ; ifuns = λ ty f d → term f d
                       ; ifuncong = fcong }
  where ≡vec : ∀ {ar}  → (ts₁ ts₂ : VecH (sorts S) (HU S) ar) →
                  _∼v_ {R = λ s₀ → _≡_} ts₁ ts₂ →
                  ts₁ ≡ ts₂
        ≡vec ⟨⟩ ⟨⟩ ≈⟨⟩ = PE.refl
        ≡vec (t ▹ ts₁) (.t ▹ ts₂) (∼▹ PE.refl ts₁≈ts₂) = PE.cong (λ ts → t ▹ ts) (≡vec ts₁ ts₂ ts₁≈ts₂)
        fcong : ∀ {ar} {s} {f : funcs S (ar , s)} → (ts₁ ts₂ : VecH (sorts S) (HU S) ar) →
                  _∼v_ {R = λ s₀ → _≡_} ts₁ ts₂ →
                  term f ts₁ ≡ term f ts₂
        fcong {ar} {s} {f} ts₁ ts₂ ts₁≈ts₂ = PE.cong (term f) (≡vec ts₁ ts₂ ts₁≈ts₂)


-- Homomorfismo del álgebra de términos a cualquier otra álgebra

mutual
  funAlgHomo : ∀ {l₁} {l₂} {S} {A : Algebra {l₁} {l₂} S} (s : sorts S) → HU S s → Carrier (isorts A s)
  funAlgHomo {S = S} {A} s (term {[]} f ⟨⟩) = ifuns A ([] , s) f ⟨⟩
  funAlgHomo {S = S} {A} s (term {s₀ ∷ ar} f (t₀ ▹ ts)) =
                 ifuns A (s₀ ∷ ar , s) f
                         ((funAlgHomo {S = S} {A} s₀ t₀) ▹ funv {S = S} {A} ar ts)

  funv : ∀ {l₁ l₂} {S} {A : Algebra {l₁} {l₂} S} (ar : Arity S) →
           VecH (sorts S) (HU S) ar → VecH (sorts S) (Carrier ∘ isorts A) ar
  funv [] ⟨⟩ = ⟨⟩
  funv {S = S} {A} (s₁ ∷ ar₁) (t₁ ▹ ts₁) = funAlgHomo {S = S} {A} s₁ t₁ ▹ funv {S = S} {A} ar₁ ts₁


-- funv es igual a mapV funAlgHomo
funv≡mapV : ∀ {l₁ l₂} {S} {A : Algebra {l₁} {l₂} S} {ar : Arity S} {ts : VecH (sorts S) (HU S) ar} →
              funv {l₁} {l₂} {S} {A} ar ts ≡ mapV (funAlgHomo {S = S} {A}) ar ts
funv≡mapV {ar = []} {⟨⟩} = PE.refl
funv≡mapV {S = S} {A} {s₀ ∷ ar} {t₀ ▹ ts} = PE.cong (λ ts' → funAlgHomo {S = S} {A} s₀ t₀ ▹ ts')
                                                funv≡mapV

tAlgHomo : ∀ {l₁ l₂} {S} → (A : Algebra {l₁} {l₂} S) → Homomorphism S (termAlgebra S) A
tAlgHomo {S = S} A = record { morph = morphAlgHomo 
                            ; preserv = hompres }
  where congfun : ∀ {s} {t₁ t₂ : HU S s} →
                  t₁ ≡ t₂ → _≈_ (isorts A s) (funAlgHomo {S = S} {A} s t₁) (funAlgHomo {S = S} {A} s t₂)
        congfun {s} {t₁} {t₂} t₁≡t₂ = ≡to≈ {St = isorts A s} (PE.cong (funAlgHomo s) t₁≡t₂)
        morphAlgHomo : FunAlg (termAlgebra S) A
        morphAlgHomo s = record { _⟨$⟩_ = funAlgHomo {S = S} {A} s
                                ; cong  = congfun}
        hompres : (ty : SType S) → (f : funcs S ty) →
                  homPreserv S (termAlgebra S) A morphAlgHomo ty f
        hompres ([] , s) f ⟨⟩ = ≡to≈ {St = isorts A s} PE.refl
        hompres (s₀ ∷ ar , s) f (t₀ ▹ ts) =
                ≡to≈ {St = isorts A s}
                     (PE.cong (λ ts' → ifuns A (s₀ ∷ ar , s) f (funAlgHomo {S = S} {A} s₀ t₀ ▹ ts'))
                              funv≡mapV)


-- El álgebra de términos es inicial
tAlgInit : ∀ {l₃ l₄} (S : Signature) → Initial {l₃ = l₃} {l₄ = l₄} S
tAlgInit {l₃} {l₄} S = record { alg = termAlgebra S
                    ; init = tinit }
  where tinit : (A : Algebra {l₃} {l₄} S) →
                Unicity (Homomorphism S (termAlgebra S) A) (_≈ₕ_)
        tinit A = tAlgHomo A , (λ h → ext (tAlgHomo A) h (uni (tAlgHomo A) h))
          where uni : (h₁ : Homomorphism S (termAlgebra S) A) →
                      (h₂ : Homomorphism S (termAlgebra S) A) →
                      (s : sorts S) → (t₁ t₂ : HU S s) →
                      t₁ ≡ t₂ →
                      _≈_ (isorts A s) (morph h₁ s ⟨$⟩ t₁) (morph h₂ s ⟨$⟩ t₂)
                uni h₁ h₂ s (term {ar} f ts) ._ PE.refl =
                    Setoid.trans (isorts A s)
                                     (preserv h₁ (ar , s) f ts)
                    (Setoid.trans (isorts A s)
                                     (ifuncong A (mapV (_⟨$⟩_ ∘ morph h₁) ar ts)
                                                 (mapV (_⟨$⟩_ ∘ morph h₂) ar ts)
                                                 (mapV≡ ar ts))
                                     (Setoid.sym (isorts A s) (preserv h₂ (ar , s) f ts)))
                  where mapV≡ : (ar : Arity S) → (ts₀ : VecH (sorts S) (HU S) ar) →
                                (mapV (_⟨$⟩_ ∘ morph h₁) ar ts₀) ∼v
                                (mapV (_⟨$⟩_ ∘ morph h₂) ar ts₀)
                        mapV≡ [] ⟨⟩ = ∼⟨⟩
                        mapV≡ (s₀ ∷ ar₀) (t₀ ▹ ts₀) = ∼▹ (uni h₁ h₂ s₀ t₀ t₀ PE.refl)
                                                          (mapV≡ ar₀ ts₀)
