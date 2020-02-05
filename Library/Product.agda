{- Product algebra -}
module Product where
open import Relation.Binary hiding (Total)
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Nat renaming (_⊔_ to _⊔ₙ_)
open import Data.Product renaming (map to pmap)
open import Function as F
open import Function.Equality as FE renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Data.Bool renaming (_≟_ to _≟b_)
open import Data.List renaming (map to lmap)
open import Relation.Binary.PropositionalEquality as PE hiding ( Reveal_·_is_;[_];isEquivalence)
open import Relation.Unary hiding (_⊆_;_⇒_)

open import Data.Fin hiding (_+_)

import Relation.Binary.EqReasoning as EqR

open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)

open import HeterogeneousVec
open import UnivAlgebra hiding (_↦_)


module ProdAlg {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
        {Σ : Signature}
       (A : Algebra {ℓ₁} {ℓ₂} Σ) 
       (B : Algebra {ℓ₃} {ℓ₄} Σ) where

  open Signature
  open Algebra
  open Setoid
  open import Setoids
  
  std : (s : sorts Σ) → Setoid _ _
  std s = ×-setoid (A ⟦ s ⟧ₛ) (B ⟦ s ⟧ₛ)
  _≈*_ : {ar : Arity Σ} → _
  _≈*_ {ar} = _≈_ (std ✳ ar)


  ≈₁ : ∀ {ar} {vs vs' : ∥ std ✳ ar ∥} 
      → vs ≈* vs' → _≈_ (_⟦_⟧ₛ A ✳ ar) (map (λ _ → proj₁) vs) (map (λ _ → proj₁) vs')
  ≈₁ {[]} ∼⟨⟩ = ∼⟨⟩
  ≈₁ {i ∷ is} (∼▹ (eq , _) equ) = ∼▹ eq (≈₁ equ)
  ≈₂ : ∀ {ar} {vs vs' : ∥ std ✳ ar ∥} 
      → vs ≈* vs' → _≈_ (_⟦_⟧ₛ B ✳ ar) (map (λ _ → proj₂) vs) (map (λ _ → proj₂) vs')
  ≈₂ {[]} ∼⟨⟩ = ∼⟨⟩
  ≈₂ {i ∷ is} (∼▹ (_ , eq) equ) = ∼▹ eq (≈₂ equ)

  {- Product of algebras -}
  _×-alg_ : Algebra {ℓ₃ ⊔ ℓ₁} {ℓ₄ ⊔ ℓ₂} Σ
  _×-alg_ = record {
            _⟦_⟧ₛ = λ s → ×-setoid (A ⟦ s ⟧ₛ) (B ⟦ s ⟧ₛ)
          ; _⟦_⟧ₒ = λ {ar} {s} f → record { _⟨$⟩_ = if f ; cong = cng f}
          }
    where if : ∀ {ar s} (f : ops Σ (ar , s)) → _ → _
          if {ar} {s} f vs =  A ⟦ f ⟧ₒ ⟨$⟩ map (λ _ → proj₁) vs
                            , B ⟦ f ⟧ₒ ⟨$⟩ map (λ _ → proj₂) vs
          cng : ∀ {ar s} (f : ops Σ (ar , s)) → {vs vs' : ∥ std ✳ ar ∥} 
              → vs ≈* vs' → _≈_ (std s) (if f vs) (if f vs')
          cng {ar} f equ = (Π.cong (_⟦_⟧ₒ A f) (≈₁ equ)) ,
                           ((Π.cong (_⟦_⟧ₒ B f) (≈₂ equ)))

  {- Projection homomorphisms -}
  open import Morphisms
  open import Data.Product.Function.NonDependent.Setoid
  open Hom
  open Homo
  π₁ : Homo _×-alg_ A
  π₁ = record { ′_′ = λ _ → proj₁ₛ ; cond = λ {_} {s} f as → Setoid.refl (A ⟦ s ⟧ₛ) }
  
  π₂ : Homo _×-alg_ B
  π₂ = record { ′_′ = λ _ → proj₂ₛ ; cond = λ {_} {s} f as → Setoid.refl (B ⟦ s ⟧ₛ) }

  module PairMor {ℓ} {ℓ'} (C : Algebra {ℓ} {ℓ'} Σ)  where
    ⟨_,_⟩ : (f : Homo C A) → (g : Homo C B) → Homo C _×-alg_
    ⟨ f , g ⟩ = record { ′_′ = λ s → < ′ f ′ s , ′ g ′ s >ₛ 
                     ; cond = λ {_} {s} ft as → hom-cond ft as
                     }
      where _≈×_ : ∀ {s : sorts Σ} → _
            _≈×_ {s} = _≈_ (_×-alg_ ⟦ s ⟧ₛ)
            fg : _
            fg x = < _⟨$⟩_ (′ f ′ x) , _⟨$⟩_ (′ g ′ x) >
            hom-cond : ∀ {s} {ar} (ft : ops Σ (ar , s)) (as : HVec _ ar) →
                     (< ′ f ′ s , ′ g ′ s >ₛ ⟨$⟩ ((C ⟦ ft ⟧ₒ) ⟨$⟩ as)) ≈× 
                                  (_×-alg_ ⟦ ft ⟧ₒ ⟨$⟩ (map (λ x → < _⟨$⟩_ (′ f ′ x) , _⟨$⟩_ (′ g ′ x) >) as))
            hom-cond {s} ft as rewrite propMapV∘ as fg (λ _ → proj₁)
                                     | propMapV∘ as fg (λ _ → proj₂) = cond f ft as , cond g ft as

