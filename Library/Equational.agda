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
open import HeterogenuousVec

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

freeness : ∀ {ℓ₁ ℓ₂} → (Σ : Signature) → (X : GroundSig (sorts Σ)) →
             (A : Algebra {ℓ₁} {ℓ₂} Σ) → (a : (s : sorts Σ) → X s → ∥ A ⟦ s ⟧ₛ ∥) →
             Unique (_≈ₕ_ (T Σ 〔 X 〕) A)
freeness Σ X A a =
           {!!} , {!!}
