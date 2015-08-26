module UnivAlgebra where

open import Relation.Binary
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Nat renaming (_⊔_ to _⊔ₙ_)
open import Data.Product hiding (map)
open import Function
open import Function.Equality renaming (_∘_ to _∘ₛ_)
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


data VecH {l : Level} (S : Signature) (A : ISorts S (Set l)) : Arity S → Set l where
  ⟨⟩  : VecH S A []
  _▹_ : ∀ {s} {ar} → A s → VecH S A ar → VecH S A (s ∷ ar)

-- Igualdad de vectores
data _≈v_ {S : Signature} {l₁ l₂ : Level} {A : ISorts S (Set l₁)} {R : (s : sorts S) → Rel (A s) l₂} :
              {ar : Arity S} → (ts₁ : VecH S A ar) → (ts₂ : VecH S A ar) → Set (l₁ ⊔ l₂) where
     ≈⟨⟩ : ⟨⟩ ≈v ⟨⟩
     ≈▹  : ∀ {s} {ar} {t₁} {t₂} {ts₁ : VecH S A ar} {ts₂ : VecH S A ar} →
           R s t₁ t₂ → _≈v_ {R = R} ts₁ ts₂ → (t₁ ▹ ts₁) ≈v (t₂ ▹ ts₂)


data _∈_ {l} {S : Signature} {A : ISorts S (Set l)} :
         ∀ {s : sorts S} {ar : Arity S} → A s → VecH S A ar → Set l where
  here : ∀ {s} {t : A s} {ar} {ts : VecH S A ar} → t ∈ (t ▹ ts)
  there : ∀ {s} {s'} {t : A s} {t' : A s'} {ar} {ts : VecH S A ar} →
            t ∈ ts → t ∈ (t' ▹ ts)


{-
  Dada la aridad de un símbolo de función f en la signatura S, el sort
  target y una función de interpretación de los sorts de S, retorna
  el tipo de la interpretación de la función f. 
-}
IFun : ∀ {l} → (S : Signature) → (ty : SType S) →
               ISorts S (Set l)  → Set l
IFun S (ar , s) i = VecH S i ar → i s


-- Algebra de una signatura S
record Algebra {l₁ l₂ : Level} (S : Signature) : 
                             Set (lsuc (l₁ ⊔ l₂)) where
  field
    isorts   : (s : sorts S) → Setoid l₁ l₂
    ifuns    : (ty : SType S) → (f : funcs S ty) → IFun S ty (Carrier ∘ isorts)
    ifuncong : ∀ {ar} {s} {f} →
               (ts₁ ts₂ : VecH S (Carrier ∘ isorts) ar) →
               _≈v_ {R = _≈_ ∘ isorts} ts₁ ts₂ →
               _≈_ (isorts s) (ifuns (ar , s) f ts₁)
                              (ifuns (ar , s) f ts₂)

open Algebra

idom : ∀ {S} {l₁} {l₂} → (ty : SType S) → (A : Algebra {l₁} {l₂} S) → Set _ 
idom {S} (ar , _) A = VecH S (Carrier ∘ isorts A) ar

-- Función many sorted entre dos álgebras
-- (Ver si este es el nombre más adecuado)
FunAlg : ∀ {S : Signature} {l₁} {l₂} →
           (A : Algebra {l₁} {l₂} S) → (A' : Algebra {l₁} {l₂} S) →
           Set _
FunAlg {S} A A' = (s : sorts S) → isorts A s ⟶ isorts A' s

mapV : ∀ {l₁} {S : Signature}
         {i : (sorts S) → Set l₁} {i' : (sorts S) → Set l₁} →
         (m : (s : sorts S) → (i s) → (i' s)) → 
         (arty : Arity S) →
         (as : VecH S i arty) →
         VecH S i' arty
mapV m [] ⟨⟩ = ⟨⟩
mapV m (s₀ ∷ rest) (is₀ ▹ irest) = m s₀ is₀ ▹ mapV m rest irest


mapMorph : ∀ {S : Signature} {l₁} {l₂}
                {A A' : Algebra {l₁} {l₂} S}
                {ty : SType S}
                (m : FunAlg A A') → (as : idom ty A) → 
                idom ty A'
mapMorph {S} {_} {_} {A} {A'} {ty = ar , s} m as = mapV (λ s → _⟨$⟩_ (m s)) ar as 

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


propMapVComp : ∀ {l₁} {S : Signature}
                 {i₀ : (sorts S) → Set l₁} {i₁ : (sorts S) → Set l₁}
                 {i₂ : (sorts S) → Set l₁} →
                 (ar : Arity S) →
                 (d : VecH S i₀ ar) →
                 (m : (s : sorts S) → (i₀ s) → (i₁ s)) →
                 (m' : (s : sorts S) → (i₁ s) → (i₂ s)) →
                 mapV m' ar (mapV m ar d)
                 ≡
                 mapV (λ s' → m' s' ∘ m s') ar d
propMapVComp [] ⟨⟩ m m' = PE.refl
propMapVComp (s₀ ∷ rest) (is₀ ▹ irest) m m' =
                   cong₂ (λ x y → x ▹ y) PE.refl
                         (propMapVComp rest irest m m')

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


Unicity : ∀ {l₁} {l₂} → (A : Set l₁) → (A → A → Set l₂) → Set _ 
Unicity A rel = Σ A (λ a → (a' : A) → rel a a')


record Initial {l₁ l₂ : Level} (S : Signature) : 
                             Set (lsuc (l₁ ⊔ l₂)) where
  field
    alg      : Algebra {l₁} {l₂} S
    init     : (A : Algebra {l₁} {l₂} S) → Unicity (Homomorphism S alg A) (_≈ₕ_)


-- Algebra de términos


-- Carriers del álgebra de términos de una signatura. HU es por Herbrand Universe.

data HU (S : Signature) : (s : sorts S) → Set where
  term : ∀ {ar} {s} → (f : funcs S (ar , s)) →
                      (ts : VecH S (HU S) ar) → HU S s

-- Tamaño de un termino HU
nterm : ∀ {S} {s : sorts S} → HU S s → ℕ
nterm (term {[]} f ⟨⟩) = zero
nterm {S} (term {s ∷ ar} f ts) = suc (maxn ts)
  where maxn : ∀ {s'} {ar'} → VecH S (HU S) (s' ∷ ar') → ℕ
        maxn {ar' = []} (t ▹ ⟨⟩) = nterm t
        maxn {ar' = s₁ ∷ ar'} (t₀ ▹ ts') = nterm t₀ ⊔ₙ maxn ts'


termAlgebra : (S : Signature) → Algebra {lzero} {lzero} S
termAlgebra S = record { isorts = PE.setoid ∘ HU S
                       ; ifuns = λ ty f d → term f d
                       ; ifuncong = {!!} }


-- Homomorfismo del álgebra de términos a cualquier otra álgebra

mutual
  funAlgHomo : ∀ {S} {A : Algebra {lzero} {lzero} S} (s : sorts S) → HU S s → Carrier (isorts A s)
  funAlgHomo {S} {A} s (term {[]} f ⟨⟩) = ifuns A ([] , s) f ⟨⟩
  funAlgHomo {S} {A }s (term {s₀ ∷ ar} f (t₀ ▹ ts)) =
                 ifuns A (s₀ ∷ ar , s) f
                         ((funAlgHomo {S} {A} s₀ t₀) ▹ funv {S} {A} ar ts)   --ifuns A (ar , s) f (mapV ar ts fun)

  funv : ∀ {S} {A : Algebra {lzero} {lzero} S} (ar : Arity S) → VecH S (HU S) ar → VecH S (Carrier ∘ isorts A) ar
  funv [] ⟨⟩ = ⟨⟩
  funv {S} {A} (s₁ ∷ ar₁) (t₁ ▹ ts₁) = funAlgHomo {S} {A} s₁ t₁ ▹ funv {S} {A} ar₁ ts₁


-- funv es igual a mapV funAlgHomo
funv≡mapV : ∀ {S} {A} {ar : Arity S} {ts : VecH S (HU S) ar} →
              funv {S} {A} ar ts ≡ mapV (funAlgHomo {S} {A}) ar ts
funv≡mapV {ar = []} {⟨⟩} = PE.refl
funv≡mapV {S} {A} {s₀ ∷ ar} {t₀ ▹ ts} = PE.cong (λ ts' → funAlgHomo {S} {A} s₀ t₀ ▹ ts')
                                                funv≡mapV

tAlgHomo : ∀ {S} → (A : Algebra {lzero} {lzero} S) → Homomorphism S (termAlgebra S) A
tAlgHomo {S} A = record { morph = morphAlgHomo 
                        ; preserv = hompres }
  where congfun : ∀ {s} {t₁ t₂ : HU S s} →
                  t₁ ≡ t₂ → _≈_ (isorts A s) (funAlgHomo {S} {A} s t₁) (funAlgHomo {S} {A} s t₂)
        congfun {s} {t₁} {t₂} t₁≡t₂ = ≡to≈ {St = isorts A s} (PE.cong (funAlgHomo s) t₁≡t₂)
        morphAlgHomo : FunAlg (termAlgebra S) A
        morphAlgHomo s = record { _⟨$⟩_ = funAlgHomo {S} {A} s
                                ; cong  = congfun}
        hompres : (ty : SType S) → (f : funcs S ty) →
                  homPreserv S (termAlgebra S) A morphAlgHomo ty f
        hompres ([] , s) f ⟨⟩ = ≡to≈ {St = isorts A s} PE.refl
        hompres (s₀ ∷ ar , s) f (t₀ ▹ ts) =
                ≡to≈ {St = isorts A s}
                     (PE.cong (λ ts' → ifuns A (s₀ ∷ ar , s) f (funAlgHomo {S} {A} s₀ t₀ ▹ ts'))
                              funv≡mapV)


-- El álgebra de términos es inicial

-- Si dos vectores son iguales entonces aplicar la interpretacion de una funcion
-- sobre dichos vectores es igual.
≈ifuns : ∀ {l₁ l₂} {S} {A : Algebra {l₁} {l₂} S} {ar} {s} {f}
           {ts₁ ts₂ : VecH S (Carrier ∘ isorts A) ar} →
           _≈v_ {R = _≈_ ∘ isorts A} ts₁ ts₂ →
         _≈_ (isorts A s)
             (ifuns A (ar , s) f ts₁)
             (ifuns A (ar , s) f ts₂)
≈ifuns {A = A} {ts₁ = ts₁} {ts₂ = ts₂} ts₁≈ts₂ = ifuncong A ts₁ ts₂ ts₁≈ts₂

{-
mapV≡ : ∀ {l₁ l₂} {S} {A : Setoid l₁ l₂} {ar} →
          (v : VecH S (Carrier A) ar) →
          (f₁ : Carrier A → Carrier A) → (f₂ : Carrier A → Carrier A) →
          (g : (a : Carrier A) → _≈_ A (f₁ a) (f₂ a)) →
          v ≈v (mapV g v ar)
mapV≡ = ?
-}
          

tAlgInit : (S : Signature) → Initial {lzero} {lzero} S
tAlgInit S = record { alg = termAlgebra S
                    ; init = tinit }
  where tinit : (A : Algebra {lzero} {lzero} S) →
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
                                     {!!} {!!})
{-                uni h₁ h₂ s (term {[]} f ⟨⟩) ._ PE.refl =
                    Setoid.trans (isorts A s)
                                 (preserv h₁ ([] , s) f ⟨⟩)
                                 (Setoid.sym (isorts A s) (preserv h₂ ([] , s) f ⟨⟩))
                uni h₁ h₂ s (term {x ∷ ar} f ts) .(term f ts) PE.refl =
                       Setoid.trans (isorts A s)
                                    {!preserv h₁ !} {!!}

-}
