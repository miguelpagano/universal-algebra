\documentclass{article}
\usepackage{agda}
\usepackage{amsmath}
\usepackage{mathpartir}


%include agda.fmt
%include unicode.fmt

\begin{document}
\begin{code}

-- Universal Algebra Library
--
-- Direct sum. This module is incomplete.
--
open import UnivAlgebra hiding (_↦_)
module DirectSum {Σ : Signature} where

open import Relation.Binary
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Product renaming (map to pmap) hiding (Σ)
open import Function as F
open import Function.Equality as FE renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Relation.Binary.PropositionalEquality as PE
open import Relation.Unary hiding (_⊆_;_⇒_)

open import HeterogeneousVec
open import Morphisms {Σ}

isSubAlgebra : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} →
             (B : Algebra {ℓ₃} {ℓ₄} Σ) → (A : Algebra {ℓ₁} {ℓ₂} Σ) → {ℓ₀ : Level} → Set _
isSubAlgebra {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} B A {ℓ₀} =
             Σ[ sub ∈ SubAlg {ℓ₀} A ] Isomorphism {ℓ₃} {ℓ₄} B (SubAlgebra sub)

isDirected : ∀ {ℓ₁ ℓ₂ ℓ₃} {I : Set ℓ₁}
             (A : I → Algebra {ℓ₂} {ℓ₃} Σ) → {ℓ₀ : Level} → Set _
isDirected A {ℓ₀} = ∀ i j → ∃ (λ k → isSubAlgebra (A i) (A k) {ℓ₀} × isSubAlgebra (A j) (A k) {ℓ₀})

module DirectSum {ℓ₁ ℓ₂ ℓ₃ ℓ₀ : Level} {I : Set ℓ₁}
             (A : I → Algebra {ℓ₂} {ℓ₃} Σ) (isDir : isDirected A {ℓ₀}) where

    open Algebra
    open Signature
    open Hom
    open import Setoids hiding (∥_∥)
    open Isomorphism
    open Homo

    _≈ᵤ_ : {s : sorts Σ} → Rel (Σ[ i ∈ I ] (A i ∥ s ∥)) ℓ₃
    _≈ᵤ_ {s} (i , a) (j , b) = ((A k ⟦ s ⟧ₛ) Setoid.≈ proj₁ (′ hom iso_i ′ s ⟨$⟩ a)) (proj₁ (′ hom iso_j ′ s ⟨$⟩ b))
      where kA : ∃ (λ k → _ × _)
            kA = isDir i j
            k : I
            k = proj₁ kA
            Ak_i : SubAlg (A k)
            Ak_i = proj₁ (proj₁ (proj₂ kA))
            iso_i : Isomorphism (A i) (SubAlgebra Ak_i)
            iso_i = proj₂ (proj₁ (proj₂ kA))
            Ak_j : SubAlg (A k)
            Ak_j = proj₁ (proj₂ (proj₂ kA))
            iso_j : Isomorphism (A j) (SubAlgebra Ak_j)
            iso_j = proj₂ (proj₂ (proj₂ kA))
{-
    ∐-setoid : (s : sorts Σ) → Setoid (ℓ₁ ⊔ ℓ₂) {!!}
    ∐-setoid s = record { Carrier = Σ[ i ∈ I ] (A i ∥ s ∥)
                        ; _≈_ = _≈ᵤ_ {s}
                        ; isEquivalence = {!!}
                        }

    ∐ : Algebra {{!!}} {{!!}} Σ
    ∐ = {!!}
-}

\end{code}
\end{document}

