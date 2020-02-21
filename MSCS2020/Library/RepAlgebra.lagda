{- Representation of Algebras -}
-- TODO
-- 1. generalizar T_Σ(X) permitiendo que X sea un setoide.
-- 2. promover T a un funtor


module RepAlgebra where

open import UnivAlgebra
open import Morphisms
open import HeterogeneousVec
open import Setoids
open import Function as F
open import Function.Equality as FE renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Relation.Binary.PropositionalEquality as PE
open import Data.Product hiding (map)
open import Relation.Binary
open import Relation.Unary hiding (_⊆_;_⇒_)
open import Data.List hiding (map)


open Signature
open Hom
open Homo
open import Function.Bijection renaming (_∘_ to _∘b_) 
open import Function.Surjection hiding (_∘_)

module RepAlg {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
        {Σ : Signature}
       (A : Algebra {ℓ₁} {ℓ₂} Σ) 
       (B : Algebra {ℓ₃} {ℓ₄} Σ) where

  [_,_] : (A ⟿ B ) → (B ⟿ A) → Set
  [ rep , abs ] = ∀ s → (a : ∥ (T A) ⟦ s ⟧ₛ ∥) → ⟦ a ⟧u id ≈_{A ⟦ s ⟧ₛ} abs (⟦ (T rep) a ⟧u id)
