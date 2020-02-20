-- Universal Algebra Library
--
-- Term algebra of ground and open terms.
--
module TermAlgebra where

open import Data.List hiding (map)
open import Data.Product hiding (map ; Σ)
open import Data.Sum hiding (map)
open import Function as F
open import Function.Equality as FE renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Level
open import Relation.Binary hiding (Total)
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.PropositionalEquality as PE

open import HeterogeneousVec
open import Morphisms
open import Setoids hiding (∥_∥)
open import UnivAlgebra

module GroundTerm  (Σ : Signature) where
  data HU : (s : sorts Σ) → Set where
    term : ∀  {ar s} →  (f : ops Σ (ar ↦ s)) → (HVec HU ar) → HU s

  open Hom

  ∣T∣ : Algebra Σ
  ∣T∣ = record
    { _⟦_⟧ₛ = setoid ∘ HU
    ; _⟦_⟧ₒ = λ f → record
               { _⟨$⟩_ = term f
               ; cong = PE.cong (term f) ∘ ≡vec
               }
    }

  open Homo
  open Setoid

  module Eval {ℓ₁ ℓ₂} (A : Algebra {ℓ₁} {ℓ₂} Σ) where
    private
      eval : ∀ {s} → HU s → A ∥ s ∥
      eval* : ∀ {ar} → ∣T∣ ∥ ar ∥* → A ∥ ar ∥*

      eval (term f ⟨⟩)         =   A ⟦ f ⟧ₒ ⟨$⟩ ⟨⟩
      eval (term f (t ▹ ts))  =   A ⟦ f ⟧ₒ ⟨$⟩ (eval t ▹ eval* ts)

      eval* ⟨⟩ = ⟨⟩
      eval* (t ▹ ts) = eval t ▹ eval* ts


      map-eval : ∀ {ar} {ts : ∣T∣ ∥ ar ∥*} → eval* ts ≡ map (λ _ → eval) ts
      map-eval {ar = []} {⟨⟩} = PE.refl
      map-eval {ar = s ∷ ar} {t ▹ ts} = PE.cong (eval t ▹_) map-eval

    ∣H∣ : Homo ∣T∣ A
    ∣H∣ = record { ′_′  = fun|T|ₕ
                ; cond = |T|ₕcond
                }
       where
       congfun : ∀ {s} {t₁ t₂ : HU s} → t₁ ≡ t₂ → _≈_ (A ⟦ s ⟧ₛ) (eval t₁) (eval t₂)
       congfun {s} t₁≡t₂ = ≡to≈ (A ⟦ s ⟧ₛ) (PE.cong (eval) t₁≡t₂)
       fun|T|ₕ : ∣T∣ ⟿ A
       fun|T|ₕ s = record { _⟨$⟩_ = eval {s = s}
                          ; cong  = congfun {s}
                          }
       |T|ₕcond : homCond ∣T∣ A fun|T|ₕ
       |T|ₕcond {_} {s} f ⟨⟩ = ≡to≈ (A ⟦ s ⟧ₛ) PE.refl
       |T|ₕcond {_} {s} f (t ▹ ts) =
                ≡to≈ (A ⟦ s ⟧ₛ) (PE.cong (λ ts' → A ⟦ f ⟧ₒ ⟨$⟩
                                (eval t ▹ ts')) map-eval)

    total : Total {Σ} (_≈ₕ_ ∣T∣ A)
    total H G s (term {ar = ar} f ts) = begin
      ′ H ′ s ⟨$⟩ term f ts                ≈⟨ cond H f ts ⟩
      A ⟦ f ⟧ₒ ⟨$⟩ (map⟿ ∣T∣ A ′ H ′ ts)  ≈⟨ Π.cong (A ⟦ f ⟧ₒ) (map≈ ar ts) ⟩
      A ⟦ f ⟧ₒ ⟨$⟩ (map⟿ ∣T∣ A ′ G ′ ts)  ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (cond G f ts) ⟩
      ′ G ′ s ⟨$⟩ term f ts ∎
      where
      open EqR (A ⟦ s ⟧ₛ)
      map≈ : (ar : Arity Σ) → (ts : HVec (HU) ar) →
             (map (_⟨$⟩_ ∘ ′ H ′) ts) ∼v (map (_⟨$⟩_ ∘ ′ G ′) ts)
      map≈ [] ⟨⟩ = ∼⟨⟩
      map≈ (s ∷ ar) (t ▹ ts) = ∼▹ (total H G s t) (map≈ ar ts)


  open Initial
  ∣T∣isInitial : ∀ {ℓ₁ ℓ₂} → Initial {ℓ₃ = ℓ₁} {ℓ₄ = ℓ₂}
  ∣T∣isInitial = record
    { alg = ∣T∣
    ; init = λ A → ∣H∣ A , total A
    }
    where open Eval

-- Extension of signature to have variables.
{- Variables symbols of a signature. In the bibliography is presented too
   as Ground Signature (signature with only constant symbols) -}
Vars : (Σ : Signature) → Set₁
Vars Σ = (s : sorts Σ) → Set

module OpenTerm (Σ : Signature) (X : Vars Σ) where

  {- Signature extension with variables -}
  _〔_〕 : Signature
  _〔_〕 = record
    { sorts = sorts Σ
    ; ops = λ { ([] , s) → ops Σ ([] , s) ⊎ X s
              ; (s' ∷ ar , s) → ops Σ (s' ∷ ar , s)
              }
    }

  {- Term Algebra of Σ (X) as Σ-Algebra -}
  T_〔_〕 :  Algebra Σ
  T_〔_〕 = record
    { _⟦_⟧ₛ = ∣T∣ ⟦_⟧ₛ
    ; _⟦_⟧ₒ = λ { {[]} {s} f → ∣T∣ ⟦ inj₁ f ⟧ₒ
                ; {s₀ ∷ ar} {s} f → ∣T∣ ⟦ f ⟧ₒ}
    }
    where open GroundTerm (_〔_〕)

  {- Environments -}
  Env : ∀ {ℓ₁ ℓ₂} → (A : Algebra {ℓ₁} {ℓ₂} Σ) → Set ℓ₁
  Env A = ∀ {s} → X s → A ∥ s ∥

  open GroundTerm (_〔_〕) hiding (module Eval) public

  var : ∀ {s} (x : X s) → T_〔_〕 ∥ s ∥
  var x = term (inj₂ x) ⟨⟩


  {- Extension of the initial homomorphism to signatures with variables -}
  module Eval {ℓ₁ ℓ₂ : Level} (A : Algebra {ℓ₁} {ℓ₂} Σ) (a : Env A) where

    open Hom
    open Homo

    eval : {s : sorts Σ} →  ∣T∣ ∥ s ∥ →  A ∥ s ∥
    eval* : ∀ {ar} → ∣T∣ ∥ ar ∥* → A ∥ ar ∥*
    eval (term {[]} (inj₁ k) ⟨⟩) = A ⟦ k ⟧ₒ ⟨$⟩ ⟨⟩
    eval (term {[]} (inj₂ x) ⟨⟩) = a x
    eval (term {_ ∷ _} f ts) = A ⟦ f ⟧ₒ ⟨$⟩ eval* ts

    eval* ⟨⟩ = ⟨⟩
    eval* (t ▹ ts) = eval t ▹ eval* ts

    open Setoid
    cong-eval : ∀ {s} {t₁ t₂ : ∣T∣ ∥ s ∥} →
                     t₁ ≡ t₂ → _≈_ (A ⟦ s ⟧ₛ) (eval t₁) (eval t₂)
    cong-eval {s} {t₁} eq = ≡to≈ (A ⟦ s ⟧ₛ) (PE.cong eval eq)
    cong-eval* : ∀ {ar} {ts : ∣T∣ ∥ ar ∥*} → eval* ts ≡ map (λ- eval) ts
    cong-eval* {ar = []} {⟨⟩} = PE.refl
    cong-eval* {ar = s ∷ ar} {t ▹ ts} = PE.cong (eval t ▹_) cong-eval*

    TΣX⇝A : T_〔_〕 ⟿ A
    TΣX⇝A s = record
      { _⟨$⟩_ = eval
      ; cong = cong-eval
      }

    ⟦_⟧ : ∀ {s} → T_〔_〕 ∥ s ∥ →  A ∥ s ∥
    ⟦_⟧ {s} = TΣX⇝A s ⟨$⟩_

    {- Homomorphism condition of TΣX⇝A -}
    TΣXcond : homCond (T_〔_〕) A TΣX⇝A
    TΣXcond {.[]} {s} f ⟨⟩ = Setoid.refl (A ⟦ s ⟧ₛ)
    TΣXcond {s₀ ∷ ar'} {s} f (t ▹ ts) =
      ≡to≈ (A ⟦ s ⟧ₛ) (PE.cong (A ⟦ f ⟧ₒ ⟨$⟩_) (cong-eval* {ts = t ▹ ts}))

    TΣXHom : Homo (T_〔_〕) A
    TΣXHom = record { ′_′ = TΣX⇝A ; cond = TΣXcond }

  module EvalUMP {ℓ₁ ℓ₂ : Level} (A : Algebra {ℓ₁} {ℓ₂} Σ) (a : Env A) where
    open Eval A a
    open Setoid
    open Hom T_〔_〕 A
    open Homo

    extends : Homo → Set _
    extends h = ∀ {s} → (x : X s) → _≈_ (A ⟦ s ⟧ₛ) ( ′ h ′ s ⟨$⟩ var x) (a x)

    tot : (H H' : Homo) → extends H → extends H' → H ≈ₕ H'
    tot H H' he he' s (term {[]} (inj₂ x) ⟨⟩) = begin
      (′ H ′ s ⟨$⟩ var x)  ≈⟨ he x ⟩
      a x                 ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (he' x) ⟩
      ′ H' ′ s ⟨$⟩ var x ∎
      where open EqR (A ⟦ s ⟧ₛ)
    tot H H' he he' s (term {[]} (inj₁ k) ⟨⟩) = begin
      ′ H ′ s ⟨$⟩ (term {[]} (inj₁ k) ⟨⟩)   ≈⟨ cond H k ⟨⟩ ⟩
      A ⟦ k ⟧ₒ ⟨$⟩ ⟨⟩                   ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (cond H' k ⟨⟩) ⟩
      ′ H' ′ s ⟨$⟩ (term (inj₁ k) ⟨⟩)  ∎
      where open EqR (A ⟦ s ⟧ₛ)
    tot H H' he he' s (term {x ∷ ar} f ts) = begin
      ′ H ′ s ⟨$⟩ term f ts             ≈⟨ cond H f ts ⟩
        A ⟦ f ⟧ₒ ⟨$⟩ (map⟿ ′ H ′ ts)   ≈⟨ Π.cong (A ⟦ f ⟧ₒ) (map≈ (x ∷ ar) ts) ⟩
        A ⟦ f ⟧ₒ ⟨$⟩ (map⟿ ′ H' ′ ts)  ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (cond H' f ts) ⟩
        ′ H' ′ s ⟨$⟩ term f ts ∎
      where
      open EqR (A ⟦ s ⟧ₛ)
      map≈ : (ar : Arity Σ) → (ts : HVec _ ar) →
             _∼v_ {R = λ {s} → _≈_ (A ⟦ s ⟧ₛ)}
                  (map (_⟨$⟩_ ∘ ′ H ′) ts)
                  (map (_⟨$⟩_ ∘ ′ H' ′) ts)
      map≈ [] ⟨⟩ = ∼⟨⟩
      map≈ (s ∷ ar) (t ▹ ts) = ∼▹ (tot H H' he he' s t) (map≈ ar ts)

  module UMP_unit where

    open Hom
    open Homo
    TX = T_〔_〕

    η-tx : Env TX
    η-tx {s} = var

    open EvalUMP TX η-tx

    HomId-extends-η : extends HomId
    HomId-extends-η x = PE.refl

    module HX = Hom TX TX

    -- If H extends η, then H ≈ₕ HomId.
    ≈ₕ-id⁺ : (H : Homo TX TX) → extends H → H HX.≈ₕ HomId
    ≈ₕ-id⁺ H ext = tot H HomId ext HomId-extends-η


  module Subst where

    Subst : Set
    Subst = Env (T_〔_〕)

    idSubst : Subst
    idSubst x = term (inj₂ x) ⟨⟩

    open Eval (T_〔_〕)

    _/s_ : {s : sorts Σ} →  ∣T∣ ∥ s ∥ → Subst → ∣T∣ ∥ s ∥
    _/s_ {s} t θ = eval θ t

    infixr 30 _/s_

    -- Identity substitution is identity.
    subst-id : ∀ {s} → (t : T_〔_〕 ∥ s ∥) → (t /s idSubst) ≡ t
    subst*-id : ∀ {ar'} → (ts : HVec (T_〔_〕 ∥_∥) ar') → eval* idSubst ts ≡ ts
    subst-id (term {[]} (inj₁ k) ⟨⟩) = _≡_.refl
    subst-id (term {[]} (inj₂ x) ⟨⟩) = _≡_.refl
    subst-id (term {s₀ ∷ ar'} f ts) = PE.cong (term f) (subst*-id ts)

    subst*-id ⟨⟩ = _≡_.refl
    subst*-id (t ▹ ts) = cong₂ (_▹_) (subst-id t) (subst*-id ts)

  open Subst
  module SubstitutionTheorem {ℓ₁ ℓ₂ : Level} (A : Algebra {ℓ₁} {ℓ₂} Σ)
    (η : Env A) (σ : Subst) where

    module IA = Eval A η renaming (⟦_⟧ to ⟦_⟧η) hiding (eval;eval*)
    open IA using (⟦_⟧η) public
    module IT = Eval (T_〔_〕) σ renaming (⟦_⟧ to ⟦_⟧σ) hiding (eval;eval*)
    open IT using (⟦_⟧σ) public
    ση : Env A
    ση x = ⟦ σ x ⟧η

    open Eval A ση renaming (⟦_⟧ to ⟦_⟧ησ) hiding (eval;eval*) public
    open Eval hiding (eval)
    open Setoid

    subst-theo : ∀ s t → _≈_ (A ⟦ s ⟧ₛ) (⟦ ⟦ t ⟧σ ⟧η)  (⟦ t ⟧ησ)
    subst-theo* : ∀ {ar} ts → _≈_ (_⟦_⟧ₛ A ✳ ar)
                  (eval* A η (eval* ((T_〔_〕) ) σ ts))
                  (eval* A ση ts)
    subst-theo* {[]} ⟨⟩ = ∼⟨⟩
    subst-theo* {s ∷ ar} (t ▹ ts) = ∼▹ (subst-theo s t) (subst-theo* ts)
    subst-theo s (term {[]} (inj₁ k) ⟨⟩) = Setoid.refl (A ⟦ s ⟧ₛ)
    subst-theo s (term {[]} (inj₂ x) ⟨⟩) = Setoid.refl (A ⟦ s ⟧ₛ)
    subst-theo s (term {s' ∷ ar} {.s} f ts) = Π.cong (A ⟦ f ⟧ₒ) (subst-theo* ts)

