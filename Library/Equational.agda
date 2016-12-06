module Equational where

open import UnivAlgebra
open import Data.List
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
  open ExtEq
  open Homo

  mutual
    TΣX→A : (s : sorts Σ) → HU s → ∥ A ⟦ s ⟧ₛ ∥
    TΣX→A s (term {[]} (inj₁ k) ⟨⟩) = A ⟦ k ⟧ₒ ⟨$⟩ ⟨⟩
    TΣX→A s (term {[]} (inj₂ x) ⟨⟩) = a s x
    TΣX→A s (term {s₀ ∷ ar'} f (t ▹ ts)) = A ⟦ f ⟧ₒ ⟨$⟩ TΣX→A s₀ t ▹ (mapTΣX→A ts)
    
    mapTΣX→A : ∀ {ar} → ∣T∣ ⟦ ar ⟧ₛ* → A ⟦ ar ⟧ₛ*
    mapTΣX→A ⟨⟩ = ⟨⟩
    mapTΣX→A {s₀ ∷ ar'} (t ▹ ts) = (TΣX→A s₀ t) ▹ mapTΣX→A ts
                                                                   
  congTΣX→A : ∀ {s} {t₁ t₂ : ∥ ∣T∣ ⟦ s ⟧ₛ ∥} →
                   t₁ ≡ t₂ → _≈_ (A ⟦ s ⟧ₛ) (TΣX→A s t₁) (TΣX→A s t₂)
  congTΣX→A {s} {t₁} eq = ≡to≈ (A ⟦ s ⟧ₛ) (PE.cong (TΣX→A s) eq)

  mapTΣX→A≡map : ∀ {ar} {ts : ∣T∣ ⟦ ar ⟧ₛ*} →
                   mapTΣX→A ts ≡ mapV TΣX→A ts
  mapTΣX→A≡map {ar = []} {⟨⟩} = PE.refl
  mapTΣX→A≡map {ar = s ∷ ar} {t ▹ ts} = PE.cong (λ ts' → TΣX→A s t ▹ ts')
                                                 mapTΣX→A≡map

  TΣX⇝A : T Σ 〔 X 〕 ⟿ A
  TΣX⇝A s = record { _⟨$⟩_ = TΣX→A s
                    ; cong = congTΣX→A }

  {- Homomorphism condition of TΣX⇝A -}
  TΣXcond : ∀ {ty} (f : ops Σ ty) → (homCond (T Σ 〔 X 〕) A) TΣX⇝A f
  TΣXcond {.[] , s} f ⟨⟩ = Setoid.refl (A ⟦ s ⟧ₛ)
  TΣXcond {s₀ ∷ ar' , s} f (t ▹ ts) =
                ≡to≈ (A ⟦ s ⟧ₛ) (PE.cong (λ ts' → A ⟦ f ⟧ₒ ⟨$⟩
                                            (TΣX⇝A s₀ ⟨$⟩ t) ▹ ts')
                               mapTΣX→A≡map)

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
--    

  freeness : Unique (_≈ₕ_ (T Σ 〔 X 〕) A)
  freeness = (record { ′_′ = TΣX⇝A ; cond = TΣXcond })
           , uniqueTΣX
