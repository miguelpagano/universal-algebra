module Equational where

open import UnivAlgebra
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Level renaming (zero to lzero ; suc to lsuc)
open import Relation.Binary hiding (Total)
open import Relation.Binary.PropositionalEquality as PE
open import Function as F
open import Function.Equality as FE renaming (_∘_ to _∘e_)
open import HeterogenuousVec renaming (map to mapV)

import Relation.Binary.EqReasoning as EqR

{- In a ground signature all operations are constants -}
GroundSig : (Sorts : Set) → Set₁
GroundSig Sorts = (s : Sorts) → Set


open Signature
_〔_〕 : (Σ : Signature) → (X : GroundSig (sorts Σ)) → Signature
Σ 〔 X 〕 = record { sorts = sorts Σ
                   ; ops = λ { ([] , s) → ops Σ ([] , s) ⊎ X s
                             ; ty → ops Σ ty
                             }
                   }

open Algebra

{- Extension of environments -}
module EnvExt {ℓ₁ ℓ₂ : Level}
              (Σ : Signature) (X : GroundSig (sorts Σ))
              (A : Algebra {ℓ₁} {ℓ₂} Σ) where

  open TermAlgebra (Σ 〔 X 〕)

  mutual
    _↪ : (a : (s : sorts Σ) → X s → ∥ A ⟦ s ⟧ₛ ∥) →
          (s : sorts Σ) → ∥ ∣T∣ ⟦ s ⟧ₛ ∥ → ∥ A ⟦ s ⟧ₛ ∥
    (a ↪) s (term {[]} (inj₁ k) ⟨⟩) = A ⟦ k ⟧ₒ ⟨$⟩ ⟨⟩
    (a ↪) s (term {[]} (inj₂ x) ⟨⟩) = a s x
    (a ↪) s (term {s₀ ∷ ar'} f (t ▹ ts)) = A ⟦ f ⟧ₒ ⟨$⟩ (a ↪) s₀ t ▹ (map↪ a ts)
    
    map↪ : ∀ {ar} → (a : (s : sorts Σ) → X s → ∥ A ⟦ s ⟧ₛ ∥) →
                     ∣T∣ ⟦ ar ⟧ₛ* → A ⟦ ar ⟧ₛ*
    map↪ a ⟨⟩ = ⟨⟩
    map↪ {s₀ ∷ ar'} a (t ▹ ts) = ((a ↪) s₀ t) ▹ map↪ a ts


T_〔_〕 : (Σ : Signature) → (X : GroundSig (sorts Σ)) →
          Algebra Σ
T Σ 〔 X 〕 = (λ s → ∣T∣ ⟦ s ⟧ₛ)
            ∥ (λ { {[]} {s} f → ∣T∣ ⟦ inj₁ f ⟧ₒ
                 ; {s₀ ∷ ar} {s} f → ∣T∣ ⟦ f ⟧ₒ })
  where open TermAlgebra (Σ 〔 X 〕)

      



open Hom
open Setoid

{- Freeness property -}
module Freeness {ℓ₁ ℓ₂ : Level}
                (Σ : Signature) (X : GroundSig (sorts Σ))
                (A : Algebra {ℓ₁} {ℓ₂} Σ)
                (a : (s : sorts Σ) → X s → ∥ A ⟦ s ⟧ₛ ∥) where


  open InitTermAlg (Σ)
  open TermAlgebra (Σ 〔 X 〕)
  open EnvExt Σ X A
  open ExtEq
  open Homo
                                                                   
  conga↪ : ∀ {s} {t₁ t₂ : ∥ ∣T∣ ⟦ s ⟧ₛ ∥} →
                   t₁ ≡ t₂ → _≈_ (A ⟦ s ⟧ₛ) ((a ↪) s t₁) ((a ↪) s t₂)
  conga↪ {s} {t₁} eq = ≡to≈ (A ⟦ s ⟧ₛ) (PE.cong ((a ↪) s) eq)

  map↪≡map : ∀ {ar} {ts : ∣T∣ ⟦ ar ⟧ₛ*} →
                   map↪ a ts ≡ mapV (a ↪) ts
  map↪≡map {ar = []} {⟨⟩} = PE.refl
  map↪≡map {ar = s ∷ ar} {t ▹ ts} = PE.cong (λ ts' → (a ↪) s t ▹ ts')
                                                 map↪≡map

  TΣX⇝A : T Σ 〔 X 〕 ⟿ A
  TΣX⇝A s = record { _⟨$⟩_ = (a ↪) s
                    ; cong = conga↪ }

  {- Homomorphism condition of TΣX⇝A -}
  TΣXcond : ∀ {ty} (f : ops Σ ty) → (homCond (T Σ 〔 X 〕) A) TΣX⇝A f
  TΣXcond {.[] , s} f ⟨⟩ = Setoid.refl (A ⟦ s ⟧ₛ)
  TΣXcond {s₀ ∷ ar' , s} f (t ▹ ts) =
                ≡to≈ (A ⟦ s ⟧ₛ) (PE.cong (λ ts' → A ⟦ f ⟧ₒ ⟨$⟩
                                            (TΣX⇝A s₀ ⟨$⟩ t) ▹ ts')
                               map↪≡map)

  uniqueTΣX : Total (T Σ 〔 X 〕 ≈ₕ A)
  uniqueTΣX H₁ H₂ s (TermAlgebra.term {[]} (inj₂ x) ⟨⟩) =
            begin
              ′ H₁ ′ s ⟨$⟩ term (inj₂ x) ⟨⟩
            ≈⟨ {!!} ⟩
              a s x
            ≈⟨ {!!} ⟩
              ′ H₂ ′ s ⟨$⟩ term (inj₂ x) ⟨⟩
            ∎
    where open EqR (A ⟦ s ⟧ₛ)
  uniqueTΣX H₁ H₂ s (TermAlgebra.term {[]} (inj₁ k) ⟨⟩) =
            begin
              ′ H₁ ′ s ⟨$⟩ term (inj₁ k) ⟨⟩
            ≈⟨ cond H₁ k ⟨⟩ ⟩
              A ⟦ k ⟧ₒ ⟨$⟩ ⟨⟩
            ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (cond H₂ k ⟨⟩) ⟩
              ′ H₂ ′ s ⟨$⟩ term (inj₁ k) ⟨⟩
            ∎
    where open EqR (A ⟦ s ⟧ₛ)
  uniqueTΣX H₁ H₂ s (TermAlgebra.term {s₀ ∷ ar} f ts) = {!!}


  freeness : Unique (_≈ₕ_ (T Σ 〔 X 〕) A)
  freeness = (record { ′_′ = TΣX⇝A ; cond = TΣXcond })
           , uniqueTΣX

open TermAlgebra

{- Equations -}

record NCEquation (Σ : Signature) (X : GroundSig (sorts Σ)) (s : sorts Σ) : Set₁ where
  constructor ⋀_≈_
  field
    left  : ∥ ∣T∣ (Σ 〔 X 〕) ⟦ s ⟧ₛ ∥
    right : ∥ ∣T∣ (Σ 〔 X 〕) ⟦ s ⟧ₛ ∥

ncsort : ∀ {Σ X} {s : sorts Σ} → NCEquation Σ X s → sorts Σ
ncsort {s = s} _ = s

open NCEquation

record CEquation (Σ : Signature) (X : GroundSig (sorts Σ)) (s : sorts Σ) : Set₁ where
  constructor _if「_」_
  field
    eq   : NCEquation Σ X s
    arty : Arity Σ
    cond : HVec (λ s' → ∥ ∣T∣ (Σ 〔 X 〕) ⟦ s' ⟧ₛ ∥ ×
                         ∥ ∣T∣ (Σ 〔 X 〕) ⟦ s' ⟧ₛ ∥) arty

csort : ∀ {Σ X} {s : sorts Σ} → CEquation Σ X s → sorts Σ
csort {s = s} _ = s

open CEquation

_-Equation : (Σ : Signature) → (X : GroundSig (sorts Σ))→ (s : sorts Σ) → Set₁
(Σ -Equation) X s = NCEquation Σ X s ⊎ CEquation Σ X s

Theory : (Σ : Signature) → (X : GroundSig (sorts Σ)) → (ar : Arity Σ) → Set₁
Theory Σ X ar = HVec ((Σ -Equation) X) ar


-- Satisfactibility
{-
Discusión: En las reglas de substitución y reemplazo, hay dos conjuntos de variables
           X e Y, para que tenga sentido debe haber una inclusión. Aquí estamos
           indexando todas las definiciones en el conjunto de variables. No debería
           haber problemas ya que en todo caso la cuantificación habla de variables
           que pueden no ocurrir en los términos.
-}

〈_,_〉_⊨_ : ∀ {ℓ₁ ℓ₂} → (Σ : Signature) → (X : GroundSig (sorts Σ)) →
                          {s : sorts Σ} → (A : Algebra {ℓ₁} {ℓ₂} Σ) →
                          (Σ -Equation) X s → Set _
〈 Σ , X 〉 A ⊨ inj₁ e = (θ : (s : sorts Σ) → X s → ∥ A ⟦ s ⟧ₛ ∥) →
                         (_≈_ (A ⟦ ncsort e ⟧ₛ)) ((θ ↪) (ncsort e) (left e))
                                                ((θ ↪) (ncsort e) (right e))
  where open EnvExt Σ X A
〈 Σ , X 〉 A ⊨ inj₂ e = (θ : (s : sorts Σ) → X s → ∥ A ⟦ s ⟧ₛ ∥) →
                     (λ { s₀ (uᵢ , uᵢ') → _≈_ (A ⟦ s₀ ⟧ₛ)
                                         ((θ ↪) s₀ uᵢ)
                                         ((θ ↪) s₀ uᵢ')}) ⇨v cond e →
                     (_≈_ (A ⟦ s ⟧ₛ)) ((θ ↪) s (left (eq e)))
                                      ((θ ↪) s (right (eq e)))
  where open EnvExt Σ X A
        s : sorts Σ
        s = csort e

record ⊨ {ℓ₁ ℓ₂ : Level} {Σ X} {ar : Arity Σ} (P : Theory Σ X ar)
                         (A : Algebra {ℓ₁} {ℓ₂} Σ) : Set₁  where
  field
    satAll : ∀ {s} {e : (Σ -Equation) X s} → e ∈ P → 〈 Σ , X 〉 A ⊨ e


open EnvExt

{- Provability -}
data 〈_,_〉_⊢_ (Σ : Signature) (X : GroundSig (sorts Σ))
                 {ar : Arity Σ} (E : HVec ((Σ -Equation) X) ar) :
                 {s : sorts Σ} → NCEquation Σ X s → Set₁  where
  prefl : ∀ {s} {t : ∥ ∣T∣ (Σ 〔 X 〕) ⟦ s ⟧ₛ ∥} → 〈 Σ , X 〉 E ⊢ (⋀ t ≈ t)
  psym : ∀ {s} {t t' : ∥ ∣T∣ (Σ 〔 X 〕) ⟦ s ⟧ₛ ∥} → 〈 Σ , X 〉 E ⊢ (⋀ t ≈ t') →
                                                 〈 Σ , X 〉 E ⊢ (⋀ t' ≈ t)
  ptrans : ∀ {s} {t₀ t₁ t₂ : ∥ ∣T∣ (Σ 〔 X 〕) ⟦ s ⟧ₛ ∥} →
                 〈 Σ , X 〉 E ⊢ (⋀ t₀ ≈ t₁) → 〈 Σ , X 〉 E ⊢ (⋀ t₁ ≈ t₂) →
                 〈 Σ , X 〉 E ⊢ (⋀ t₀ ≈ t₂)
  psubst : ∀ {s} {ar} {us : HVec (λ s' → ∥ ∣T∣ (Σ 〔 X 〕) ⟦ s' ⟧ₛ ∥ ×
                                          ∥ ∣T∣ (Σ 〔 X 〕) ⟦ s' ⟧ₛ ∥) ar}
           {t t' : ∥ ∣T∣ (Σ 〔 X 〕) ⟦ s ⟧ₛ ∥} →
           inj₂ ((⋀ t ≈ t') if「 ar 」 us) ∈ E →
           (θ : (s' : sorts Σ) → X s' → ∥ ∣T∣ (Σ 〔 X 〕) ⟦ s' ⟧ₛ ∥) →
           (⊢us : (λ { s₀ (uᵢ , uᵢ') →
                   〈 Σ , X 〉 E ⊢ (⋀ _↪ Σ X (T Σ 〔 X 〕) θ s₀ uᵢ ≈
                                   _↪ Σ X (T Σ 〔 X 〕) θ s₀ uᵢ') }) ⇨v us) →
           〈 Σ , X 〉 E ⊢ (⋀ t ≈ t')
  preemp : ∀ {ar'} {s} {es : HVec (NCEquation Σ X) ar'} → (σ : ops (Σ 〔 X 〕) (ar' , s)) →
             〈 Σ , X 〉 E ⊢ (⋀ term σ (mapV (λ sᵢ e → left e) es) ≈
                                 term σ (mapV (λ sᵢ e → right e) es)
                             ) 

