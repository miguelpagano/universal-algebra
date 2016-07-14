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
open import Data.String
open import Data.Fin

open import VecH

open Setoid


{-
Discusión: Aquí estamos indexando a los símbolos de función en el tipo de los mismos
(lista de sorts x sorts), otra opción podría ser tener indexado por los sorts resultado
primero y luego en la lista de sorts, así podríamos referirnos a todos los símbolos de
función con resultado en determinado sort. En alguna bibliografía se usa esta última
noción.
-}

Sorts : Set _
Sorts = Set

Funcs : Sorts → Set _
Funcs S = (List S) × S → Set

record Signature : Set₁ where
  field
    sorts  : Sorts
    funcs  : Funcs sorts

  Arity : Set
  Arity = List sorts

  ΣType : Set
  ΣType = List sorts × sorts

open Signature

arty : ∀ {Σ} {ar} {s} → (f : funcs Σ (ar , s)) → Arity Σ
arty {ar = ar} f = ar

tgt : ∀ {Σ} {ar} {s} → (f : funcs Σ (ar , s)) → sorts Σ
tgt {s = s} f = s

{-
  Tipo que representa la interpretación de un sort de
  la signatura S.
-}
ISorts : ∀ {ℓ₁ ℓ₂} → (Σ : Signature) → Set _
ISorts {ℓ₁} {ℓ₂} Σ = (sorts Σ) → Setoid ℓ₁ ℓ₂

IFuncs : ∀ {ℓ₁ ℓ₂} → (Σ : Signature) → (ty : ΣType Σ) →
         ISorts {ℓ₁} {ℓ₂} Σ → Set _
IFuncs Σ (ar , s) is = VecSet (sorts Σ) is ar ⟶ is s

-- Algebra de una signatura Σ
record Algebra {ℓ₁ ℓ₂ : Level} (Σ : Signature) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  constructor _∥_
  field
    _⟦_⟧ₛ    : ISorts {ℓ₁} {ℓ₂} Σ
    _⟦_⟧    : ∀ {ty : ΣType Σ} → (f : funcs Σ ty) → IFuncs Σ ty _⟦_⟧ₛ

open Algebra


idom : ∀ {Σ} {ℓ₁} {ℓ₂} → (ar : Arity Σ) → (A : Algebra {ℓ₁} {ℓ₂} Σ) → Set _ 
idom {Σ} ar A = VecH (sorts Σ) (Carrier ∘ _⟦_⟧ₛ A) ar


-- Función entre dos álgebras
_⟿_ : ∀ {Σ : Signature} {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} →
         (A : Algebra {ℓ₁} {ℓ₂} Σ) → (A' : Algebra {ℓ₃} {ℓ₄} Σ) →
         Set _
_⟿_ {Σ} A A' = (s : sorts Σ) → A ⟦ s ⟧ₛ ⟶ A' ⟦ s ⟧ₛ


-- Map de una función entre álgebras a un vector heterogéneo
map⟿ : ∀ {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} {Σ : Signature} 
                {A : Algebra {ℓ₁} {ℓ₂} Σ} {A' : Algebra {ℓ₃} {ℓ₄} Σ}
                {ar : Arity Σ} →
                (m : A ⟿ A') → (ts : idom ar A) → idom ar A'
map⟿ {ar = ar} m ts = mapV (_⟨$⟩_ ∘ m) ts

{- 
   Definición de la condición de homomorfismo para una función A ⟿ A'
-}
homCond : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Σ : Signature} {ty : ΣType Σ} →
            (A : Algebra {ℓ₁} {ℓ₂} Σ) → (A' : Algebra {ℓ₃} {ℓ₄} Σ) →
            (h : A ⟿ A') → (f : funcs Σ ty) → Set _
homCond {Σ = Σ} {ty = (ar , s)} A A' h f =
           (as : idom ar A) → _≈_ (A' ⟦ s ⟧ₛ)
                                  (h s ⟨$⟩ (A ⟦ f ⟧ ⟨$⟩ as))
                                  (A' ⟦ f ⟧ ⟨$⟩ (map⟿ {Σ = Σ} {A} {A'} h as))

--Homomorfismo.

record Homomorphism {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Σ : Signature}
                    (A : Algebra {ℓ₁} {ℓ₂} Σ) (A' : Algebra {ℓ₃} {ℓ₄} Σ) : 
                                    Set (lsuc (ℓ₄ ⊔ ℓ₃ ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    ′_′    : A ⟿ A'
    cond   : ∀ {ty} (f : funcs Σ ty) → homCond A A' ′_′ f

open Homomorphism

{-
Propiedad de igualdad extensional para dos funciones f y g
-}
ExtProp : ∀ {ℓ₁ ℓ₂ ℓ₁' ℓ₂'} {A : Set ℓ₁} {B : Set ℓ₂} →
            Rel A ℓ₁' → Rel B ℓ₂' → (f : A → B) → (g : A → B) → Set _
ExtProp {A = A} _≈A_ _≈B_ f g = (a a' : A) → a ≈A a' → f a ≈B g a'


-- -- Igualdad de homomorfismos
data _≈ₕ_ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Σ} {A : Algebra {ℓ₁} {ℓ₂} Σ} {A' : Algebra {ℓ₃} {ℓ₄} Σ}
          (H H' : Homomorphism A A') : Set (lsuc (ℓ₄ ⊔ ℓ₃ ⊔ ℓ₁ ⊔ ℓ₂)) where
  ext : ((s : sorts Σ) → ExtProp (_≈_ (A ⟦ s ⟧ₛ)) (_≈_ (A' ⟦ s ⟧ₛ))
                                 (_⟨$⟩_ (′ H ′ s)) (_⟨$⟩_ (′ H' ′ s))) →
        H ≈ₕ H'


elim≈ₕ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Σ} {A : Algebra {ℓ₁} {ℓ₂} Σ} {A' : Algebra {ℓ₃} {ℓ₄} Σ} →
          {H H' : Homomorphism A A'} → (H ≈ₕ H') →
          (s : sorts Σ) → (a b : Carrier (A ⟦ s ⟧ₛ)) → _≈_ (A ⟦ s ⟧ₛ) a b →
            _≈_ (A' ⟦ s ⟧ₛ) (′ H ′ s ⟨$⟩ a) (′ H' ′ s ⟨$⟩ b)
elim≈ₕ (ext eq) s a b = eq s a b


≡to≈ : ∀ {ℓ₁} {ℓ₂} {St : Setoid ℓ₁ ℓ₂} {x y : Carrier St} →
       x ≡ y → _≈_ St x y
≡to≈ {St = St} PE.refl = Setoid.refl St


import Relation.Binary.EqReasoning as EqR


-- Composición de homomorfismos
_∘ₕ_ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ l₅ l₆} {Σ} {A₀ : Algebra {ℓ₁} {ℓ₂} Σ}
         {A₁ : Algebra {ℓ₃} {ℓ₄} Σ} {A₂ : Algebra {l₅} {l₆} Σ} →
       (H₁ : Homomorphism A₁ A₂) → (H₀ : Homomorphism A₀ A₁) →
       Homomorphism A₀ A₂
_∘ₕ_ {Σ = Σ} {A₀} {A₁} {A₂} H₁ H₀ =
               record { ′_′   = comp
                      ; cond  = ∘ₕcond }
  where comp = λ s → ′ H₁ ′ s ∘ₛ ′ H₀ ′ s
        ∘ₕcond :  ∀ {ty} (f : funcs Σ ty) → homCond A₀ A₂ comp f
        ∘ₕcond {ar , s} f as =
               begin
                 comp s ⟨$⟩ (A₀ ⟦ f ⟧ ⟨$⟩ as)
                   ≈⟨ Π.cong (′ H₁ ′ s) (p₀ as) ⟩
                 ′ H₁ ′ s ⟨$⟩ (A₁ ⟦ f ⟧ ⟨$⟩ (map⟿ {A = A₀} {A' = A₁} ′ H₀ ′ as))
                   ≈⟨ p₁ (map⟿ {A = A₀} {A' = A₁} ′ H₀ ′ as) ⟩
                 A₂ ⟦ f ⟧ ⟨$⟩ (map⟿ {A = A₁} {A' = A₂} ′ H₁ ′
                                     (map⟿ {A = A₀} {A' = A₁} ′ H₀ ′ as))
                   ≈⟨ propMapMorph ⟩
                 A₂ ⟦ f ⟧ ⟨$⟩ map⟿ {A = A₀} {A' = A₂} comp as
               ∎
          where open EqR (A₂ ⟦ s ⟧ₛ)
                ty = (ar , s)
                p₁ = cond H₁ f
                p₀ = cond H₀ f
                propMapMorph =
                    begin
                      A₂ ⟦ f ⟧ ⟨$⟩ (map⟿ {A = A₁} {A' = A₂} ′ H₁ ′ $
                                         map⟿ {A = A₀} {A' = A₁} ′ H₀ ′ as)
                        ≈⟨ ≡to≈ {St = A₂ ⟦ s ⟧ₛ}
                                $ PE.cong (_⟨$⟩_ (_⟦_⟧ A₂ f))
                                          (propMapV∘ ar as (_⟨$⟩_ ∘ ′ H₀ ′)
                                                           (_⟨$⟩_ ∘ ′_′ H₁)) ⟩
                      A₂ ⟦ f ⟧ ⟨$⟩ (map⟿ {A = A₀} {A' = A₂} comp as)
                    ∎


-- Los homomorfismos forman un setoide respecto a la igualdad ≈ₕ.
hrefl : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Σ} {A₁ : Algebra {ℓ₁} {ℓ₂} Σ} {A₂ : Algebra {ℓ₃} {ℓ₄} Σ} →
                          (H₁ : Homomorphism A₁ A₂) → H₁ ≈ₕ H₁
hrefl {A₂ = A₂} H₁ = ext (λ s a b a=b → Π.cong (′ H₁ ′ s) a=b)

hsym : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Σ} {A₁ : Algebra {ℓ₁} {ℓ₂} Σ} {A₂ : Algebra {ℓ₃} {ℓ₄} Σ} →
                          (H₁ H₂ : Homomorphism A₁ A₂) → H₁ ≈ₕ H₂ → H₂ ≈ₕ H₁
hsym {Σ = Σ} {A₁} {A₂} H₁ H₂ eq = ext equ
  where equ : (s : sorts Σ) → (a b : Carrier (A₁ ⟦ s ⟧ₛ)) →
              _≈_ (A₁ ⟦ s ⟧ₛ) a b →
              _≈_ (A₂ ⟦ s ⟧ₛ) (′ H₂ ′ s ⟨$⟩ a) (′ H₁ ′ s ⟨$⟩ b)
        equ s a b a=b = Setoid.sym (A₂ ⟦ s ⟧ₛ)
                               (elim≈ₕ eq s b a (Setoid.sym (A₁ ⟦ s ⟧ₛ) a=b))

htrans : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Σ} {A₁ : Algebra {ℓ₁} {ℓ₂} Σ} {A₂ : Algebra {ℓ₃} {ℓ₄} Σ} →
                          (H₁ H₂ H₃ : Homomorphism A₁ A₂) →
                           H₁ ≈ₕ H₂ → H₂ ≈ₕ H₃ → H₁ ≈ₕ H₃
htrans {Σ = Σ} {A₁} {A₂} H₁ H₂ H₃ eq eq' = ext equ
  where equ : (s : sorts Σ) → (a b : Carrier (A₁ ⟦ s ⟧ₛ)) →
              _≈_ (A₁ ⟦ s ⟧ₛ) a b → _
        equ s a b a=b = Setoid.trans (A₂ ⟦ s ⟧ₛ)
                                 (elim≈ₕ eq s a a (Setoid.refl (A₁ ⟦ s ⟧ₛ) {x = a}))
                                 (elim≈ₕ eq' s a b a=b)



-- Definición de unicidad
Unicity : ∀ {ℓ₁} {ℓ₂} → (A : Set ℓ₁) → Rel A ℓ₂ → Set _ 
Unicity A _≈_ = Σ[ a ∈ A ] ((a' : A) → a ≈ a')


-- Álgebra inicial
record Initial {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} (Σ : Signature) : 
                             Set (lsuc (ℓ₄ ⊔ ℓ₃ ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    alg      : Algebra {ℓ₁} {ℓ₂} Σ
    init     : (A : Algebra {ℓ₃} {ℓ₄} Σ) → Unicity (Homomorphism alg A) (_≈ₕ_)

  homInit : (A : Algebra Σ) → Homomorphism alg A
  homInit A = proj₁ (init A)

  unique : (A : Algebra Σ) (h₁ h₂ : Homomorphism alg A) → h₁ ≈ₕ h₂
  unique A h₁ h₂ = htrans h₁ (homInit A) h₂ h₁≈i i≈h₂
    where h₁≈i : _
          h₁≈i = hsym (homInit A) h₁ (proj₂ (init A) h₁)
          i≈h₂ : _
          i≈h₂ = proj₂ (init A) h₂


-- Algebra de términos


-- Carriers del álgebra de términos de una signatura. HU es por Herbrand Universe.
data HU (Σ : Signature) : (s : sorts Σ) → Set where
  term : ∀ {ar} {s} → (f : funcs Σ (ar , s)) →
                      (ts : VecH (sorts Σ) (HU Σ) ar) → HU Σ s


∣T∣ : (Σ : Signature) → Algebra {lzero} {lzero} Σ
∣T∣ Σ = record { _⟦_⟧ₛ = PE.setoid ∘ HU Σ
                       ; _⟦_⟧  = λ f → termFuns f
                       }
  where ≡vec : ∀ {ar}  → (ts₁ ts₂ : VecH (sorts Σ) (HU Σ) ar) →
                  _∼v_ {R = λ s₀ → _≡_} ts₁ ts₂ →
                  ts₁ ≡ ts₂
        ≡vec ⟨⟩ ⟨⟩ ≈⟨⟩ = PE.refl
        ≡vec (t ▹ ts₁) (.t ▹ ts₂) (∼▹ PE.refl ts₁≈ts₂) =
                                  PE.cong (λ ts → t ▹ ts) (≡vec ts₁ ts₂ ts₁≈ts₂)
        fcong : ∀ {ar} {s} {f : funcs Σ (ar , s)} →
                           (ts₁ ts₂ : VecH (sorts Σ) (HU Σ) ar) →
                           _∼v_ {R = λ s₀ → _≡_} ts₁ ts₂ →
                           term f ts₁ ≡ term f ts₂
        fcong {f = f} ts₁ ts₂ ts₁≈ts₂ = PE.cong (term f) (≡vec ts₁ ts₂ ts₁≈ts₂)
        termFuns : ∀ {ar} {s} → (f : funcs Σ (ar , s)) →
                   VecSet (sorts Σ) (PE.setoid ∘ HU Σ) ar ⟶ PE.setoid (HU Σ s)
        termFuns f = record { _⟨$⟩_ = term f
                            ; cong = λ {ts₁} {ts₂} ts₁≈ts₂ → fcong ts₁ ts₂ ts₁≈ts₂
                            }

                              


-- Homomorfismo del álgebra de términos a cualquier otra álgebra

mutual
  ∣T∣→A : ∀ {ℓ₁} {ℓ₂} {Σ} {A : Algebra {ℓ₁} {ℓ₂} Σ}
                       (s : sorts Σ) → HU Σ s → Carrier (A ⟦ s ⟧ₛ)
  ∣T∣→A {A = A} s (term {[]} f ⟨⟩) = A ⟦ f ⟧ ⟨$⟩ ⟨⟩
  ∣T∣→A {A = A} s (term {s₀ ∷ _} f (t₀ ▹ ts)) =
                 A ⟦ f ⟧ ⟨$⟩ (∣T∣→A {A = A} s₀ t₀) ▹ map∣T∣→A {A = A} ts

  map∣T∣→A : ∀ {ℓ₁ ℓ₂} {Σ} {A : Algebra {ℓ₁} {ℓ₂} Σ} {ar : Arity Σ} →
           VecH (sorts Σ) (HU Σ) ar → VecH (sorts Σ) (Carrier ∘ _⟦_⟧ₛ A) ar
  map∣T∣→A {ar = []} ⟨⟩ = ⟨⟩
  map∣T∣→A {Σ = Σ} {A} {ar = s₁ ∷ _} (t₁ ▹ ts₁) =
            ∣T∣→A {Σ = Σ} {A} s₁ t₁ ▹ map∣T∣→A {Σ = Σ} {A} ts₁



-- map∣T∣→A es igual a mapV ∣T∣→A
map∣T∣→A≡mapV : ∀ {ℓ₁ ℓ₂} {Σ} {A : Algebra {ℓ₁} {ℓ₂} Σ} {ar : Arity Σ}
                          {ts : VecH (sorts Σ) (HU Σ) ar} →
              map∣T∣→A {A = A} ts ≡ mapV (∣T∣→A {A = A}) ts
map∣T∣→A≡mapV {ar = []} {⟨⟩} = PE.refl
map∣T∣→A≡mapV {A = A} {s₀ ∷ ar} {t₀ ▹ ts} =
               PE.cong (λ ts' → ∣T∣→A {A = A} s₀ t₀ ▹ ts') map∣T∣→A≡mapV



∣T∣ₕ : ∀ {ℓ₁ ℓ₂} {Σ} → (A : Algebra {ℓ₁} {ℓ₂} Σ) → Homomorphism (∣T∣ Σ) A
∣T∣ₕ {Σ = Σ} A = record { ′_′  = fun∣T∣ₕ
                       ; cond = ∣T∣ₕcond }
  where congfun : ∀ {s} {t₁ t₂ : HU Σ s} →
                  t₁ ≡ t₂ → _≈_ (A ⟦ s ⟧ₛ) (∣T∣→A {Σ = Σ} {A} s t₁) (∣T∣→A {Σ = Σ} {A} s t₂)
        congfun {s} {t₁} {t₂} t₁≡t₂ = ≡to≈ {St = A ⟦ s ⟧ₛ} (PE.cong (∣T∣→A s) t₁≡t₂)
        fun∣T∣ₕ : ∣T∣ Σ ⟿ A
        fun∣T∣ₕ s = record { _⟨$⟩_ = ∣T∣→A {A = A} s
                                ; cong  = congfun}
        ∣T∣ₕcond : ∀ {ty} (f : funcs Σ ty) →
                  homCond (∣T∣ Σ) A fun∣T∣ₕ f
        ∣T∣ₕcond {[] , s} f ⟨⟩ = ≡to≈ {St = A ⟦ s ⟧ₛ} PE.refl
        ∣T∣ₕcond {s₀ ∷ ar , s} f (t₀ ▹ ts) =
                ≡to≈ {St = A ⟦ s ⟧ₛ}
                     (PE.cong (λ ts' → A ⟦ f ⟧ ⟨$⟩ (∣T∣→A {A = A} s₀ t₀ ▹ ts'))
                              map∣T∣→A≡mapV)


-- El álgebra de términos es inicial
∣T∣init : ∀ {ℓ₁ ℓ₂} (Σ : Signature) → Initial {ℓ₃ = ℓ₁} {ℓ₄ = ℓ₂} Σ
∣T∣init {ℓ₁} {ℓ₂} Σ = record { alg = ∣T∣ Σ
                              ; init = tinit }
  where tinit : (A : Algebra {ℓ₁} {ℓ₂} Σ) →
                Unicity (Homomorphism (∣T∣ Σ) A) (_≈ₕ_)
        tinit A = ∣T∣ₕ A , (λ h → ext (uni (∣T∣ₕ A) h))
          where uni : (h₁ : Homomorphism (∣T∣ Σ) A) →
                      (h₂ : Homomorphism (∣T∣ Σ) A) →
                      (s : sorts Σ) → (t₁ t₂ : HU Σ s) → t₁ ≡ t₂ →
                      _≈_ (A ⟦ s ⟧ₛ) (′ h₁ ′ s ⟨$⟩ t₁) (′ h₂ ′ s ⟨$⟩ t₂)
                uni h₁ h₂ s (term {ar} f ts) ._ PE.refl =
                          begin
                            ′ h₁ ′ s ⟨$⟩ term f ts
                              ≈⟨ cond h₁ f ts ⟩
                            A ⟦ f ⟧ ⟨$⟩ (map⟿ {A = ∣T∣ Σ} {A' = A}
                                               ′ h₁ ′ ts)
                              ≈⟨ Π.cong (A ⟦ f ⟧) (mapV≡ ar ts) ⟩
                            A ⟦ f ⟧ ⟨$⟩ (map⟿ {A = ∣T∣ Σ} {A' = A}
                                               ′ h₂ ′ ts)
                              ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (cond h₂ f ts) ⟩ 
                            ′ h₂ ′ s ⟨$⟩ term f ts
                          ∎
                  where open EqR (A ⟦ s ⟧ₛ)
                        mapV≡ : (ar : Arity Σ) → (ts₀ : VecH (sorts Σ) (HU Σ) ar) →
                                (mapV (_⟨$⟩_ ∘ ′ h₁ ′) ts₀) ∼v
                                (mapV (_⟨$⟩_ ∘ ′ h₂ ′) ts₀)
                        mapV≡ [] ⟨⟩ = ∼⟨⟩
                        mapV≡ (s₀ ∷ ar₀) (t₀ ▹ ts₀) =
                                                ∼▹ (uni h₁ h₂ s₀ t₀ t₀ PE.refl)
                                                   (mapV≡ ar₀ ts₀)
