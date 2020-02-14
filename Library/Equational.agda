{- (conditional) equational logic: Signature with variables, environments,
   equations, equational theories, proofs, models, Birkhoff soundness and 
   completeness. -}

module Equational where

open import UnivAlgebra
open import Morphisms
open import Data.List
open import Data.Product
open import Data.Sum
open import Level renaming (zero to lzero ; suc to lsuc)
open import Relation.Binary hiding (Total)
open import Relation.Binary.PropositionalEquality as PE
open import Function as F
open import Function.Equality as FE renaming (_∘_ to _∘e_)
open import HeterogeneousVec renaming (map to mapV)

import TermAlgebra
import Relation.Binary.EqReasoning as EqR

{- Variables symbols of a signature. In the bibliography is presented too
   as Ground Signature (signature with only constant symbols) -}

𝓥 : ∀ {lsig lops} → (Σ : Sign lsig lops) → (l : Level) → Set _
𝓥 Σ l = (s : sorts Σ) → Set l

Vars : ∀ {lsig lops} → (Σ : Sign lsig lops) → Set _
Vars Σ = 𝓥 Σ lzero

open import Data.Unit.Polymorphic
{- Signature extension with variables -}
_〔_〕 : ∀ {lsig lops lvars} → (Σ : Sign lsig lops) → (X : 𝓥 Σ lvars) → Sign lsig (lops ⊔ lvars)
_〔_〕 {lvars = lvars} Σ X = record { sorts = sorts Σ
                   ; ops = λ { ([] , s) → ops Σ ([] , s) ⊎ X s
                             ; (s' ∷ ar , s) → ops Σ (s' ∷ ar , s) × ⊤ {lvars}
                             }
                   }

{- Term Algebra of Σ (X) as Σ-Algebra -}
T_〔_〕 : ∀ {lsig lops lvars} → (Σ : Sign lsig lops) → (X : 𝓥 Σ lvars) →
          Alg {ℓ₁ = lsig ⊔ (lops ⊔ lvars)} Σ 
T Σ 〔 X 〕 = record { _⟦_⟧ₛ = ∣T∣ ⟦_⟧ₛ
                    ;  _⟦_⟧ₒ = λ { {[]} {s} f → ∣T∣ ⟦ inj₁ f ⟧ₒ
                             ; {s₀ ∷ ar} {s} f → ∣T∣ ⟦ f , tt ⟧ₒ } 
                    }
  where open TermAlgebra (Σ 〔 X 〕)

open import Setoids
{- Environments -}
Env : ∀ {ℓ₁ ℓ₂ lsig lops} {Σ : Sign lsig lops} {lvars} → (X : 𝓥 Σ lvars) → (A : Alg {ℓ₁} {ℓ₂} Σ) → Set _
Env {Σ = Σ} X A = ∀ {s} → X s → ∥ A ⟦ s ⟧ₛ ∥

{- Extension of environments to terms -}
module EnvExt {ℓ₁ ℓ₂ lsig lops lvars : Level} {Σ : Sign lsig lops} (X : 𝓥 Σ lvars)
              (A : Alg {ℓ₁} {ℓ₂} Σ) where

  open TermAlgebra (Σ 〔 X 〕)

  mutual
    _↪ : (a : Env X A) → {s : sorts Σ} → ∥ ∣T∣ ⟦ s ⟧ₛ ∥ → ∥ A ⟦ s ⟧ₛ ∥
    (a ↪) (term {[]} (inj₁ k) ⟨⟩) = A ⟦ k ⟧ₒ ⟨$⟩ ⟨⟩
    (a ↪) (term {[]} (inj₂ x) ⟨⟩) = a x
    (a ↪) (term {s₀ ∷ ar'} (f , tt) ts) = A ⟦ f ⟧ₒ ⟨$⟩ (map↪ a ts)

    
    map↪ : ∀ {ar} → (a : Env X A) → ∣T∣ ⟦ ar ⟧ₛ* → A ⟦ ar ⟧ₛ*
    map↪ a ⟨⟩ = ⟨⟩
    map↪ {s₀ ∷ ar'} a (t ▹ ts) = ((a ↪) t) ▹ map↪ a ts

module Subst {lsig lops} {Σ : Sign lsig lops} {lvars} {X : 𝓥 Σ lvars} where

  Subst : Set _
  Subst = Env X (T Σ 〔 X 〕)

  open TermAlgebra (Σ 〔 X 〕)

  idSubst : Subst
  idSubst = λ x → term (inj₂ x) ⟨⟩


  open EnvExt X (T Σ 〔 X 〕)

  _/s_ : {s : sorts Σ} → ∥ ∣T∣ ⟦ s ⟧ₛ ∥ → Subst → ∥ ∣T∣ ⟦ s ⟧ₛ ∥
  _/s_ {s} t θ = (θ ↪) t

  infixr 30 _/s_

  mutual
    idSubst≡ : ∀ {s} → (t : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥) → (t /s idSubst) ≡ t
    idSubst≡ (term {[]} (inj₁ k) ⟨⟩) = _≡_.refl
    idSubst≡ (term {[]} (inj₂ x) ⟨⟩) = _≡_.refl
    idSubst≡ (term {s₀ ∷ ar'} f ts) = PE.cong (term f) (map↪id ts)

    map↪id : ∀ {ar'} → (ts : HVec (λ s' → ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) ar') →
             map↪ idSubst ts ≡ ts
    map↪id ⟨⟩ = _≡_.refl
    map↪id (t ▹ ts) = cong₂ (_▹_) (idSubst≡ t) (map↪id ts)


open Hom
open Homo
open Setoid


{- Extension of the initial homomorphism to signatures with variables -}
module InitHomoExt {ℓ₁ ℓ₂ lsig lops lvars : Level}
                {Σ : Sign lsig lops} {X : 𝓥 Σ lvars}
                (A : Alg {ℓ₁} {ℓ₂} Σ)
                (a : Env X A) where

  open TermAlgebra (Σ 〔 X 〕) renaming (∣T∣ to ∣T∣x)
  open EnvExt X A
  open ExtEq
  open Homo

  conga↪ : ∀ {s} {t₁ t₂ : ∥ ∣T∣x ⟦ s ⟧ₛ ∥} →
                   t₁ ≡ t₂ → _≈_ (A ⟦ s ⟧ₛ) ((a ↪) t₁) ((a ↪) t₂)
  conga↪ {s} {t₁} eq = ≡to≈ (A ⟦ s ⟧ₛ) (PE.cong (a ↪) eq)
  map↪≡map : ∀ {ar} {ts : ∣T∣x ⟦ ar ⟧ₛ*} →
         map↪ a ts ≡ mapV (λ s → (a ↪) {s}) ts
  map↪≡map {ar = []} {⟨⟩} = PE.refl
  map↪≡map {ar = s ∷ ar} {t ▹ ts} = PE.cong ((a ↪) t ▹_) map↪≡map
 
  TΣX⇝A : T Σ 〔 X 〕 ⟿ A
  TΣX⇝A s = record { _⟨$⟩_ = (a ↪)
                   ; cong = conga↪
                   }
 
  ⟦_⟧ : ∀ {s} → ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥ → ∥ A ⟦ s ⟧ₛ ∥
  ⟦_⟧ {s} = TΣX⇝A s ⟨$⟩_ 


  {- Homomorphism condition of TΣX⇝A -}
  TΣXcond : homCond (T Σ 〔 X 〕) A TΣX⇝A
  TΣXcond {.[]} {s} f ⟨⟩ = Setoid.refl (A ⟦ s ⟧ₛ)
  TΣXcond {s₀ ∷ ar'} {s} f (t ▹ ts) = ≡to≈ (A ⟦ s ⟧ₛ) (PE.cong (A ⟦ f ⟧ₒ ⟨$⟩_) (map↪≡map {ts = t ▹ ts}))

  TΣXHom : Homo (T Σ 〔 X 〕) A
  TΣXHom = record { ′_′ = TΣX⇝A ; cond = TΣXcond }

  HomEnv : Homo (T Σ 〔 X 〕) A → Set _
  HomEnv h = (s : sorts Σ) → (x : X s) → _≈_ (A ⟦ s ⟧ₛ) ( ′ h ′ s ⟨$⟩ term (inj₂ x) ⟨⟩ ) (a x)

 
  tot : (H H' : Homo (T Σ 〔 X 〕) A) → HomEnv H → HomEnv H' →
                                         _≈ₕ_ (T Σ 〔 X 〕) A H  H'
  tot H H' he he' s (TermAlgebra.term {[]} (inj₂ x) ⟨⟩) = begin (′ H ′ s ⟨$⟩ term (inj₂ x) ⟨⟩)
                                                          ≈⟨ he s x ⟩
                                                          a x
                                                          ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (he' s x) ⟩
                                                          ′ H' ′ s ⟨$⟩ term (inj₂ x) ⟨⟩
                                                          ∎
    where open EqR (A ⟦ s ⟧ₛ)
  tot H H' he he' s (TermAlgebra.term {[]} (inj₁ k) ⟨⟩) =
                  begin
                    ′ H ′ s ⟨$⟩ term (inj₁ k) ⟨⟩
                   ≈⟨ cond H k ⟨⟩ ⟩
                    A ⟦ k ⟧ₒ ⟨$⟩ ⟨⟩
                   ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (cond H' k ⟨⟩) ⟩
                    ′ H' ′ s ⟨$⟩ term (inj₁ k) ⟨⟩
                   ∎
    where open EqR (A ⟦ s ⟧ₛ)
  tot H H' he he' s (TermAlgebra.term {x ∷ ar} (f , tt) ts) =
                  begin
                    ′ H ′ s ⟨$⟩ term (f , tt) ts
                  ≈⟨ cond H f ts ⟩
                    A ⟦ f ⟧ₒ ⟨$⟩ (map⟿ (T Σ 〔 X 〕) A ′ H ′ ts)
                  ≈⟨ Π.cong (A ⟦ f ⟧ₒ) (map≈ (x ∷ ar) ts) ⟩
                    A ⟦ f ⟧ₒ ⟨$⟩ (map⟿ (T Σ 〔 X 〕) A ′ H' ′ ts)
                  ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (cond H' f ts) ⟩ 
                    ′ H' ′ s ⟨$⟩ term (f , tt) ts
                  ∎
    where open EqR (A ⟦ s ⟧ₛ)
          map≈ : (ar : Arity Σ) → (ts : HVec (HU) ar) →
                 _∼v_ {R = _≈_ ∘ (_⟦_⟧ₛ A)} (mapV (_⟨$⟩_ ∘ ′ H ′) ts) (mapV (_⟨$⟩_ ∘ ′ H' ′) ts)
          map≈ [] ⟨⟩ = ∼⟨⟩
          map≈ (s ∷ ar) (t ▹ ts) = ∼▹ (tot H H' he he' s t)
                                      (map≈ ar ts)


open Subst
module SubstitutionTheorem {ℓ₁ ℓ₂ lsig lops lvars : Level}
                {Σ : Sign lsig lops} {X : 𝓥 Σ lvars}
                {A : Alg {ℓ₁} {ℓ₂} Σ}
                (η : Env X A)
                (σ : Subst {Σ = Σ} {X = X})
                where
       module IA = InitHomoExt A η renaming (⟦_⟧ to ⟦_⟧η) 
       open IA using (⟦_⟧η) public
       module IT = InitHomoExt (T Σ 〔 X 〕)  σ renaming (⟦_⟧ to ⟦_⟧σ)
       open IT using (⟦_⟧σ) public
       _∘ₑ_ : Env X A
       _∘ₑ_ x = ⟦ σ x ⟧η

       open InitHomoExt A _∘ₑ_ renaming (⟦_⟧ to ⟦_⟧ησ) public
       open TermAlgebra
       open EnvExt
       subst-theo : ∀ s t → _≈_ (A ⟦ s ⟧ₛ) (⟦ ⟦ t ⟧σ ⟧η)  (⟦ t ⟧ησ)
       subst-theo* : ∀ {ar} ts → _≈_ (_⟦_⟧ₛ A ✳ ar) (map↪ X A η (map↪ X ((T Σ 〔 X 〕) ) σ ts)) (map↪ X A _∘ₑ_ ts)
       subst-theo* {[]} ⟨⟩ = ∼⟨⟩
       subst-theo* {s ∷ ar} (t ▹ ts) = ∼▹ (subst-theo s t) (subst-theo* ts)
       subst-theo s (term {[]} (inj₁ k) ⟨⟩) = Setoid.refl (A ⟦ s ⟧ₛ)
       subst-theo s (term {[]} (inj₂ x) ⟨⟩) = Setoid.refl (A ⟦ s ⟧ₛ)
       subst-theo s (term {s' ∷ ar} {.s} (f , tt) ts) = Π.cong (A ⟦ f ⟧ₒ) (subst-theo* ts)

open TermAlgebra

{- Equations -}
record Equation {lsig lops lvars} (Σ : Sign lsig lops) (X : 𝓥 Σ lvars) (s : sorts Σ)
       : Set (lsuc (lsig ⊔ lops ⊔ lvars)) where
  constructor ⋀_≈_if「_」_
  field
    left  : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥
    right : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥
    carty : Arity Σ
    cond : HVec (λ s' → ∥ ∣T∣ (Σ 〔 X 〕) ⟦ s' ⟧ₛ ∥) carty ×
           HVec (λ s' → ∥ ∣T∣ (Σ 〔 X 〕) ⟦ s' ⟧ₛ ∥) carty

{- Unconditional equation -}
⋀_≈_ : ∀ {lsig lops lvars} {Σ : Sign lsig lops} {X : 𝓥 Σ lvars} {s} → (t t' : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥) → Equation Σ X s
⋀ t ≈ t' = ⋀ t ≈ t' if「 [] 」 (⟨⟩ , ⟨⟩)

infix 0 ⋀_≈_

record Equ {lsig lops lvars} (Σ : Sign lsig lops) (X : 𝓥 Σ lvars) (s : sorts Σ) :  Set (lsuc (lsig ⊔ lops ⊔ lvars))  where
  field
    left  : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥
    right : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥

Theory : ∀ {lsig lops lvars} → (Σ : Sign lsig lops) → (X : 𝓥 Σ lvars) → (ar : Arity Σ) →  Set (lsuc (lsig ⊔ lops ⊔ lvars)) 
Theory Σ X ar = HVec (Equation Σ X) ar

equ-to-Equation : ∀ {lsig lops lvars} {Σ : Sign lsig lops} {X : 𝓥 Σ lvars} s → Equ Σ X s → Equation Σ X s
equ-to-Equation _ equ = ⋀ (left equ) ≈ (right equ)
  where open Equ
  
EqTheory : ∀ {lsig lops lvars} → (Σ : Sign lsig lops) → (X : 𝓥 Σ lvars) → (ar : Arity Σ) → Set (lsuc (lsig ⊔ lops ⊔ lvars))
EqTheory Σ X ar = HVec (Equ Σ X) ar

eqTheory-to-Theory : ∀ {lsig lops lvars} {Σ : Sign lsig lops} {X : 𝓥 Σ lvars} {ar} → EqTheory Σ X ar → Theory Σ X ar
eqTheory-to-Theory = mapV equ-to-Equation 

equation-to-Equ : ∀ {lsig lops lvars}{Σ : Sign lsig lops} {X : 𝓥 Σ lvars} s → Equation Σ X s → Equ Σ X s
equation-to-Equ _ equ = record { left = left equ ; right = right equ }
  where open Equation

iso-equ : ∀ {lsig lops lvars}{Σ : Sign lsig lops} {X : 𝓥 Σ lvars} s → (eq : Equ Σ X s) →
        eq ≡ equation-to-Equ s (equ-to-Equation s eq)
iso-equ s record { left = t ; right = t' } = PE.refl
  where open Equ


{- Satisfactibility -}
_⊨_ : ∀ {lsig lops lvars ℓ₁ ℓ₂}{Σ : Sign lsig lops} {X : 𝓥 Σ lvars} {s : sorts Σ} →
        (A : Alg {ℓ₁} {ℓ₂} Σ) → Equation Σ X s → Set (lsig ⊔ lops ⊔ lvars ⊔ ℓ₂ ⊔ ℓ₁)
_⊨_ {X = X} {s} A (⋀ t ≈ t' if「 _ 」 (us , us')) =
    (θ : Env X A) →
    _∼v_ {R = λ sᵢ uᵢ uᵢ' → _≈_ (A ⟦ sᵢ ⟧ₛ) ((θ ↪) uᵢ) ((θ ↪) uᵢ')} us us' →
    (_≈_ (A ⟦ s ⟧ₛ)) ((θ ↪) t) ((θ ↪) t')
    
  where open EnvExt X A


{- A is model -}
_⊨T_ : ∀ {ℓ₁ ℓ₂ lsig lops lvars} {Σ : Sign lsig lops} {X : 𝓥 Σ lvars} {ar} → (A : Alg {ℓ₁} {ℓ₂} Σ) →
             (E : Theory Σ X ar) → Set _
A ⊨T E = ∀ {s e} → _∈_ {i = s} e E → A ⊨ e

⊨All : ∀ {ℓ₁ ℓ₂ lsig lops lvars}{Σ : Sign lsig lops} {X : 𝓥 Σ lvars} {ar : Arity Σ} {s : sorts Σ} → (E : Theory Σ X ar) →
               (e : Equation Σ X s) → Set (lsuc (lsig ⊔ lops ⊔ lvars ⊔  ℓ₂ ⊔  ℓ₁))
⊨All {ℓ₁} {ℓ₂} {Σ = Σ} E e = (A : Alg {ℓ₁} {ℓ₂} Σ) → A ⊨T E → A ⊨ e


{- Provability -}
data _⊢_ {lsig lops lvars}{Σ : Sign lsig lops} {X : 𝓥 Σ lvars}
         {ar : Arity Σ} (E : Theory Σ X ar) :
          {s : sorts Σ} → Equation Σ X s → Set (lsuc (lsig ⊔ lops ⊔ lvars)) where
  prefl : ∀ {s} {t : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥} → E ⊢ (⋀ t ≈ t)
  psym : ∀ {s} {t t' : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥} → E ⊢ (⋀ t ≈ t') →
                                                  E ⊢ (⋀ t' ≈ t)
  ptrans : ∀ {s} {t₀ t₁ t₂ : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥} →
                 E ⊢ (⋀ t₀ ≈ t₁) → E ⊢ (⋀ t₁ ≈ t₂) → E ⊢ (⋀ t₀ ≈ t₂)
  psubst : ∀ {s} {ar'} {us us' : HVec (λ s' → ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) ar'}
           {t t' : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥} →
           (⋀ t ≈ t' if「 ar' 」 (us , us')) ∈ E →
           (σ : Subst) →
           _∼v_ {R = λ sᵢ uᵢ uᵢ' → E ⊢ (⋀ uᵢ /s σ ≈ uᵢ' /s σ)} us us' →
           E ⊢ (⋀ t /s σ ≈ t' /s σ )
  preemp : ∀ {ar'} {s} {ts ts' : HVec (λ s' → ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) ar'} →
             _∼v_ {R = λ sᵢ tᵢ tᵢ' → E ⊢ (⋀ tᵢ ≈ tᵢ')} ts ts' →
             {f : ops (Σ 〔 X 〕) (ar' , s)} → E ⊢ (⋀ term f ts ≈ term f ts') 


-- Syntactic sugar
_∣_ : ∀ {lsig lops lvars}{Σ : Sign lsig lops} {X : 𝓥 Σ lvars} {ar : Arity Σ} {E : Theory Σ X ar} {s}
           {t t' : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥} →
           (⋀ t ≈ t') ∈ E → (σ : Subst) →
           E ⊢ (⋀ t /s σ ≈ t' /s σ)
ax ∣ σ = psubst ax σ ∼⟨⟩


{- Birkhoff soundness and completeness -}
soundness : ∀ {ℓ₁ ℓ₂ lsig lops lvars}{Σ : Sign lsig lops} {X : 𝓥 Σ lvars}
              {ar : Arity Σ} {s : sorts Σ} {E : Theory Σ X ar}
                {e : Equation Σ X s} → E ⊢ e → ⊨All {ℓ₁} {ℓ₂} E e
soundness {s = s} prefl A _ _ _ = Setoid.refl (A ⟦ s ⟧ₛ)
soundness {s = s} {E} (psym t₁≈t₀) A A⊨E θ ∼⟨⟩ = 
             Setoid.sym (A ⟦ s ⟧ₛ) (soundness t₁≈t₀ A A⊨E θ ∼⟨⟩)
soundness {X = X} {ar} {s} {E} (ptrans t₀≈t₁ t₁≈t₂) A x θ ∼⟨⟩ =
             Setoid.trans (A ⟦ s ⟧ₛ)
               (soundness t₀≈t₁ A x θ ∼⟨⟩)
               (soundness t₁≈t₂ A x θ ∼⟨⟩) 
soundness {Σ = Σ} {X} {ar} {s} {E}
            (psubst {t = t} {t'} e∈E σ ⊢us≈us') A A⊨E θ ∼⟨⟩ = begin
                 ⟦ ⟦ t ⟧σ ⟧θ
              ≈⟨ subst-theo s t ⟩
                 ⟦ t ⟧θσ
              ≈⟨ A⊨E e∈E θ∘σ (
                 map∼v (λ {s₀} {uᵢ} {uᵢ'} eq → A-trans (A-sym (subst-theo s₀ uᵢ))
                                             (A-trans eq (subst-theo s₀ uᵢ')) ) (IHus θ ⊢us≈us')) ⟩ 
                 ⟦ t' ⟧θσ
              ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (subst-theo s t') ⟩
                 ⟦ ⟦ t' ⟧σ ⟧θ
              ∎
  where open EqR (A ⟦ s ⟧ₛ)
        A-sym : ∀ {s} {i j} → _ → _ 
        A-sym {s} {i} {j} eq = Setoid.sym (A ⟦ s ⟧ₛ) {i} {j} eq
        A-trans : ∀ {s} {i j k} → _ → _ → _
        A-trans {s} {i} {j} {k} eq eq' = Setoid.trans (A ⟦ s ⟧ₛ) {i} {j} {k} eq eq'
        open SubstitutionTheorem {A = A} θ σ renaming (⟦_⟧ησ to ⟦_⟧θσ;⟦_⟧η to ⟦_⟧θ;_∘ₑ_ to θ∘σ)
        open EnvExt X A 
        IHus : ∀ {ar₀} {us₀ us₀' : HVec (λ s' → ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) ar₀} →
               (θ' : Env X A) → 
               _∼v_ {R = λ sᵢ uᵢ uᵢ' → E ⊢ (⋀ uᵢ /s σ ≈  uᵢ' /s σ )} us₀ us₀' →
               _∼v_ {R = λ sᵢ uᵢ uᵢ' → (A ⟦ sᵢ ⟧ₛ ≈ (θ' ↪) (uᵢ /s σ))
                                                 ((θ' ↪) (uᵢ' /s σ))} us₀ us₀'
        IHus θ' ∼⟨⟩ = ∼⟨⟩
        IHus θ' (∼▹ ⊢u₁≈u₂ ⊢us₁≈us₂) = ∼▹ (soundness ⊢u₁≈u₂ A A⊨E θ' ∼⟨⟩) (IHus θ' ⊢us₁≈us₂)

soundness {s = s} {E} (preemp {[]} ∼⟨⟩ {f}) A A⊨E θ ∼⟨⟩ = Setoid.refl (A ⟦ s ⟧ₛ)
soundness {ℓ₁} {ℓ₂} {Σ = Σ} {X} {ar} {s} {E}
            (preemp {x ∷ ar'} {.s} {ts} {ts'} ⊢ts≈ts' {f , tt}) A A⊨E θ ∼⟨⟩ =
                begin
                   (θ ↪) (term (f , tt) ts)
                 ≈⟨ TΣXcond f ts ⟩
                   A ⟦ f ⟧ₒ ⟨$⟩ map⟿ (T Σ 〔 X 〕) A TΣX⇝A ts
                 ≈⟨ Π.cong (A ⟦ f ⟧ₒ) (map≈ (IHts ⊢ts≈ts')) ⟩
                   A ⟦ f ⟧ₒ ⟨$⟩ map⟿ (T Σ 〔 X 〕) A TΣX⇝A ts'
                 ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (TΣXcond f ts') ⟩
                   (θ ↪) (term (f , tt) ts')
                ∎
                
  where open EqR (A ⟦ s ⟧ₛ)
        open InitHomoExt A θ
        open EnvExt X A 
        IHts : ∀ {ar₀} {ts₀ ts₀' : HVec (λ s' → ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) ar₀} →
               _∼v_ {R = λ sᵢ tᵢ tᵢ' → E ⊢ (⋀ tᵢ ≈ tᵢ')} ts₀ ts₀' →
               _∼v_ {R = λ sᵢ tᵢ tᵢ' → (A ⟦ sᵢ ⟧ₛ ≈ (θ ↪) tᵢ)
                                                 ((θ ↪) tᵢ')} ts₀ ts₀'
        IHts {[]} {⟨⟩} ∼⟨⟩ = ∼⟨⟩
        IHts {s₀ ∷ ar₀} {t₀ ▹ ts₀} {t₀' ▹ ts₀'} (∼▹ ⊢t₀≈t₀' ⊢ts₀≈ts₀') =
                                    ∼▹ (ih ⊢t₀≈t₀' A A⊨E θ ∼⟨⟩) (IHts ⊢ts₀≈ts₀')
          where ih : ∀ {s' : sorts Σ} {tᵢ tᵢ' : ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥} →
                       E ⊢ (⋀ tᵢ ≈ tᵢ') → ⊨All E (⋀ tᵢ ≈ tᵢ')
                ih {s'} {tᵢ} {tᵢ'} peq = soundness peq
        map≈ : ∀ {ar'} {ts₀ ts₀' : HVec (λ s' → ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) ar'} →
               (p : _∼v_ {R = λ sᵢ tᵢ tᵢ' → (A ⟦ sᵢ ⟧ₛ ≈ (θ ↪) tᵢ)
                                                 ((θ ↪) tᵢ')} ts₀ ts₀') →
               _∼v_ {R = λ s₀ → _≈_ (A ⟦ s₀ ⟧ₛ)}
               (map⟿ (T Σ 〔 X 〕) A TΣX⇝A ts₀) (map⟿ (T Σ 〔 X 〕) A TΣX⇝A ts₀')
        map≈ {[]} ∼⟨⟩ = ∼⟨⟩
        map≈ {i ∷ is} {t₀ ▹ ts₀} {t₀' ▹ ts₀'} (∼▹ p₀ p) = ∼▹ p₀ (map≈ p)


-- Completeness
⊢R : ∀ {lsig lops lvars}{Σ : Sign lsig lops} {X : 𝓥 Σ lvars} {ar} → (E : Theory Σ X ar) → (s : sorts Σ) →
       Rel (∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥) (lsuc lsig ⊔ lsuc lops ⊔ lsuc lvars)
⊢R E s t t' = E ⊢ (⋀ t ≈ t') 

⊢REquiv : ∀ {lsig lops lvars}{Σ : Sign lsig lops} {X : 𝓥 Σ lvars} {ar} → (E : Theory Σ X ar) → (s : sorts Σ) →
          IsEquivalence (⊢R E s)
⊢REquiv E s = record { refl = prefl
                     ; sym = psym
                     ; trans = ptrans
                     }

⊢RSetoid : ∀ {lsig lops lvars}{Σ : Sign lsig lops} {X : 𝓥 Σ lvars} {ar} → (E : Theory Σ X ar) → (s : sorts Σ)
           → Setoid (lsig ⊔ lops ⊔ lvars) (lsuc (lsig ⊔ lops ⊔ lvars))
⊢RSetoid {Σ = Σ} {X} {ar} E s = record { Carrier = ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥
                                   ; _≈_ = ⊢R E s
                                   ; isEquivalence = ⊢REquiv E s
                                   }

⊢Cong : ∀ {lsig lops lvars}{Σ : Sign lsig lops} {X : 𝓥 Σ lvars} {ar} → (E : Theory Σ X ar) → Congruence (T Σ 〔 X 〕)
⊢Cong {Σ = Σ} {X} E = record { rel = ⊢R E
               ; welldef = pwdef
               ; cequiv = ⊢REquiv E
               ; csubst = pcsubst }
  where pwdef : ∀ s → WellDefRel (T Σ 〔 X 〕 ⟦ s ⟧ₛ) (⊢R E s)
        pwdef s {(t , t')} {(.t , .t')} (PE.refl , PE.refl) ⊢t₀≈t₁ = ⊢t₀≈t₁
        pcsubst : ∀ {ar} {s} → (f : ops Σ (ar , s)) →
                    _∼v_ =[ _⟨$⟩_ (T Σ 〔 X 〕 ⟦ f ⟧ₒ) ]⇒ ⊢R E s
        pcsubst {[]} f ∼⟨⟩ = prefl
        pcsubst {s₀ ∷ ar} {s} f {ts} {ts'} ⊢ts≈ts' = preemp ⊢ts≈ts' {f , tt}
        
⊢Quot : ∀ {lsig lops lvars}{Σ : Sign lsig lops} {X : 𝓥 Σ lvars} {ar} → (E : Theory Σ X ar) →
        Alg {(lsig ⊔ lops ⊔ lvars)} {(lsuc lsig ⊔ lsuc lops ⊔ lsuc lvars)} Σ
⊢Quot {Σ = Σ} {X} E = T Σ 〔 X 〕 / (⊢Cong E)

module ⊢QuotSubst {lsig lops lvars}{Σ : Sign lsig lops} {X : 𝓥 Σ lvars} {ar} (E : Theory Σ X ar) where
  open EnvExt X (⊢Quot E)
  open EnvExt X (T Σ 〔 X 〕) hiding (_↪) renaming (map↪ to map↪ₜ)

  mutual
    thm : ∀ {s : sorts Σ} {t} {θ : Subst} → (t /s θ) ≡ ((θ ↪) t)
    thm {t = term (inj₁ k) ⟨⟩} {θ} = _≡_.refl
    thm {t = term (inj₂ x) ⟨⟩} {θ} = _≡_.refl
    thm {t = term f (t ▹ ts)} {θ} = PE.cong (term f) (thm' {ts = t ▹ ts} {θ} )

    thm' : ∀ {ar'} {ts : HVec (HU (Σ 〔 X 〕)) ar' } {θ : Subst} → map↪ₜ θ ts ≡ map↪ θ ts
    thm' {ts = ⟨⟩} {θ} = _≡_.refl
    thm' {s ∷ ar} {ts = v ▹ ts} {θ} = cong₂ _▹_ (thm {s} {t = v} {θ}) (thm' {ts = ts} {θ})


⊢Quot⊨E : ∀ {lsig lops lvars}{Σ : Sign lsig lops} {X : 𝓥 Σ lvars} {ar} → (E : Theory Σ X ar) → (⊢Quot E) ⊨T E
⊢Quot⊨E {Σ = Σ} {X} {ar} E = A⊨E
  where
    open EnvExt X (⊢Quot E)
    open EnvExt X (T Σ 〔 X 〕) hiding (_↪) renaming (map↪ to map↪ₜ)
    open ⊢QuotSubst E
    
    A⊨E : ∀ {s} {e : Equation Σ X s} → _∈_ {is = ar} e E → (⊢Quot E) ⊨ e
    A⊨E {s} {e = ⋀ t ≈ t' if「 ar' 」 ( us , us') } e∈E θ us~us' =
                Congruence.welldef (⊢Cong E) s (thm {s = s} {t} {θ} , thm {s = s} {t'} {θ}) equi 
          where open EqR (⊢RSetoid E s)
                equi : E ⊢ (⋀ t /s θ ≈ t' /s θ)
                equi = psubst {us = us} {us'} e∈E θ
                                (map∼v (λ {s'} {t₁} {t₂} → Congruence.welldef (⊢Cong E) s'
                                ((Setoid.sym (_⟦_⟧ₛ T Σ 〔 X 〕 s') (thm {t = t₁} {θ})) ,
                                  (Setoid.sym (_⟦_⟧ₛ T Σ 〔 X 〕 s') (thm {t = t₂} {θ})))) us~us')



complete : ∀ {lsig lops lvars}{Σ : Sign lsig lops} {X : 𝓥 Σ lvars}
             {ar : Arity Σ} {s : sorts Σ} {E : Theory Σ X ar}
             {t t' : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥ } →
             ⊨All {(lops ⊔ lsig ⊔ lvars)} {lsuc (lops ⊔ lsig ⊔ lvars)} E (⋀ t ≈ t') → E ⊢ (⋀ t ≈ t')
complete {Σ = Σ} {X} {ar} {s} {E} {t} {t'} A⊨E = begin t
                  ≈⟨ ≡to≈ (⊢RSetoid E s) (PE.sym (idSubst≡ t)) ⟩
                  t /s idSubst
                  ≈⟨ Congruence.welldef (⊢Cong E ) s
                    ((Setoid.sym ((_⟦_⟧ₛ T Σ 〔 X 〕 s)) (thm {t = t} {idSubst})) ,
                    ((Setoid.sym ((_⟦_⟧ₛ T Σ 〔 X 〕 s)) (thm {t = t'} {idSubst}))))
                      (A⊨E (⊢Quot E) (⊢Quot⊨E E) idSubst ∼⟨⟩) ⟩
                  t' /s idSubst
                  ≈⟨ ≡to≈ (⊢RSetoid E s) ((idSubst≡ t')) ⟩
                  t' ∎
  where
   open EqR (⊢RSetoid E s)
   open EnvExt X (⊢Quot E)
   open EnvExt X (T Σ 〔 X 〕) hiding (_↪) renaming (map↪ to map↪ₜ)
   open ⊢QuotSubst E   

  
{- Theory implication -}
_⇒T_ : ∀ {lsig lops lvars}{Σ : Sign lsig lops} {X : 𝓥 Σ lvars} {ar ar'} →
     Theory Σ X ar → Theory Σ X ar' → Set (lsuc lsig ⊔ lsuc lops ⊔ lsuc lvars)
_⇒T_ {Σ = Σ} {X} T₁ T₂ = ∀ {s} {ax : Equation Σ X s} → ax ∈ T₂ → T₁ ⊢ ax


⊨T⇒ : ∀ {ℓ₁ ℓ₂} {lsig lops lvars}{Σ : Sign lsig lops} {X : 𝓥 Σ lvars} {ar ar'} → (T₁ : Theory Σ X ar) (T₂ : Theory Σ X ar')
        (p⇒ : T₁ ⇒T T₂) → (A : Alg {ℓ₁} {ℓ₂} Σ) → A ⊨T T₁ → A ⊨T T₂
⊨T⇒ T₁ T₂ p⇒ A satAll = λ ax → soundness (p⇒ ax) A satAll

{- Initiality of Quotiened Term Algebra -}
module InitialityModel {lsig lops lvars}{Σ : Sign lsig lops} {X : 𝓥 Σ lvars} {ar ℓ₁ ℓ₂} (E : Theory Σ X ar)
       (A : Alg {ℓ₁} {ℓ₂} Σ) (M : A ⊨T E)
          where

  import Morphisms
  open Hom
  open Homo

  init : (θ : Env X A) → Hom.Homo (⊢Quot E) A
  init θ = record { ′_′ = λ s → record { _⟨$⟩_ = _⟨$⟩_ ( ′ TΣXHom ′ s)
                                     ; cong = λ {j} {i} E⊢e → soundness E⊢e A M θ ∼⟨⟩
                                     }
                ; cond = λ f as → TΣXcond f as
                }
       where open InitHomoExt A θ

