module Variety where

open import Level renaming (zero to lzero ; suc to lsuc)
open import UnivAlgebra
open import Equational
open import Product
open import Morphisms

open Signature
open ProdAlg
open Hom

AlgClass : ∀ {ℓ₀ ℓ₁} Σ → Set (lsuc (ℓ₀ ⊔ ℓ₁))
AlgClass {ℓ₀} {ℓ₁} Σ = Algebra {ℓ₀} {ℓ₁} Σ → Set (ℓ₀ ⊔ ℓ₁)

_∈_ : ∀ {ℓ₀ ℓ₁ Σ} → Algebra {ℓ₀} {ℓ₁} Σ → AlgClass {ℓ₀} {ℓ₁} Σ → Set _
A ∈ C = C A

{- AlgClass Equality -}
record _≋_ {ℓ₀ ℓ₁ Σ} (C₁ : AlgClass {ℓ₀} {ℓ₁} Σ)
                     (C₂ : AlgClass {ℓ₀} {ℓ₁} Σ) : Set (lsuc (ℓ₀ ⊔ ℓ₁)) where
  field
    ≋to   : (A : Algebra {ℓ₀} {ℓ₁} Σ) → A ∈ C₁ → A ∈ C₂
    ≋from : (A : Algebra {ℓ₀} {ℓ₁} Σ) → A ∈ C₂ → A ∈ C₁
  

ModClass : ∀ {ℓ₀ ℓ₁ Σ X ar} → (E : Theory Σ X ar) → AlgClass {ℓ₀} {ℓ₁} Σ
ModClass E = _⊨T E


{- Definition 2.2.6 Sanella foundations -}
record EqDefClass {ℓ₀ ℓ₁} Σ (C : AlgClass {ℓ₀} {ℓ₁} Σ) :
                            Set (lsuc (ℓ₀ ⊔ ℓ₁)) where
  field
    vars : Vars Σ
    ar   : Arity Σ
    th   : Theory Σ vars ar
    eq   : C ≋ (ModClass th)



SClosed : ∀ {ℓ₀ Σ} → AlgClass {ℓ₀} {ℓ₀} Σ → Set (lsuc ℓ₀)
SClosed {ℓ₀} {Σ} C = (A : Algebra {ℓ₀} {ℓ₀} Σ) → A ∈ C →
                     (B : SubAlg {ℓ₀} A) → (SubAlgebra B) ∈ C

PClosed : ∀ {ℓ₀ Σ} → AlgClass {ℓ₀} {ℓ₀} Σ → Set (lsuc ℓ₀)
PClosed {ℓ₀} {Σ} C = (A B : Algebra {ℓ₀} {ℓ₀} Σ) →
                     A ∈ C → B ∈ C → (A ×-alg B) ∈ C 

HClosed : ∀ {ℓ₀ Σ} → AlgClass {ℓ₀} {ℓ₀} Σ → Set (lsuc ℓ₀)
HClosed {ℓ₀} {Σ} C = (A B : Algebra {ℓ₀} {ℓ₀} Σ) → (h : Homo A B) →
                     A ∈ C → (homImg A h) ∈ C

record Variety {ℓ₀} (Σ : Signature) (C : AlgClass {ℓ₀} {ℓ₀} Σ) :
                                    Set (lsuc ℓ₀) where
  field
    h    : HClosed C
    s    : SClosed C
    p    : PClosed C
