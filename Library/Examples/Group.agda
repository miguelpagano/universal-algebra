module Examples.Group where


open import UnivAlgebra
open import Equational
open import AlgTransf
open import Data.Unit hiding (setoid)
open import Data.List
open import Data.Product
open import Data.Nat
open import Data.Sum
open import HeterogeneousVec renaming (map to vmap)
open import Setoids

open Signature
open Algebra
open Hom

open import Examples.Monoid
data op-grp : List ⊤ × ⊤ → Set where
  _⁻¹ : op-grp ([ tt ] ↦ tt)

open import Data.Empty

ops-grp : List ⊤ × ⊤ → Set
ops-grp ([] , tt) = op-mon ([] , tt)
ops-grp (tt ∷ [] , tt) = op-grp ([ tt ] , tt)
ops-grp (tt ∷ tt ∷ [] , tt) = op-mon (tt ∷ [ tt ] , tt)
ops-grp (tt ∷ tt ∷ _ ∷ _ , tt) = ⊥

Σ-grp : Signature
Σ-grp = record { sorts = ⊤ ; ops = ops-grp }

module GrpTheory where
  open Theory
  -- Axioms

  Eq-grp : Set
  Eq-grp = Equation Σ-grp X tt

  open TermAlgebra

  
  -- A formula is a term of the Term Algebra
  Form-grp : Set
  Form-grp = HU (Σ-grp 〔 X 〕) tt

  toGrpF : Form → Form-grp
  toGrpF (term {[]} {.tt} (inj₁ e) x₁) = term (inj₁ e) ⟨⟩
  toGrpF (term {[]} {.tt} (inj₂ y) x) = term (inj₂ y) ⟨⟩
  toGrpF (term {.tt ∷ .(tt ∷ [])} {.tt} op (v ▹ v₁ ▹ ⟨⟩)) = term op ((toGrpF v) ▹ ((toGrpF v₁) ▹ ⟨⟩))

  toGrpEq : Eq₁ → Eq-grp
  toGrpEq (⋀ left ≈ right if「 carty 」 (us , us')) =
    ⋀ (toGrpF left) ≈ (toGrpF right) if「 carty 」 (vmap (λ i x → toGrpF x) us , vmap (λ i x → toGrpF x) us')
    
  module _ where
    -- smart constructors
    _∘_ : Form-grp → Form-grp → Form-grp
    a ∘ b = term op ⟨⟨ a , b ⟩⟩

    _⁻ : Form-grp → Form-grp
    a ⁻ = term _⁻¹ (⟪ a ⟫)
    

    open Smartcons hiding (_∘_)
    invLeft : Eq-grp
    invLeft = ⋀ (toGrpF x) ∘ ((toGrpF x) ⁻) ≈ toGrpF u if「 [] 」 (⟨⟩ , ⟨⟩)

    invRight : Eq-grp
    invRight = ⋀ ((toGrpF x) ⁻) ∘ (toGrpF x) ≈ toGrpF u if「 [] 」 (⟨⟩ , ⟨⟩)

    MonTheory' : _
    MonTheory' = vmap (λ _ eq → toGrpEq eq) MonTheory

    GrpTheory : Theory Σ-grp X (tt ∷ tt ∷ tt ∷ tt ∷ [ tt ])
    GrpTheory = invRight ▹ (invLeft ▹ MonTheory')

    pattern invR-ax = here
    pattern invL-ax = there here
    pattern ass-ax  = there (there here)
    pattern unitL-ax = there (there (there here ))
    pattern unitR-ax = there (there (there (there here)))
    

    module Proofs₁ where
        open ProvSetoid {Σ-grp} {X} 
        open import Relation.Binary.EqReasoning (ProvSetoid GrpTheory tt)
        open Subst {Σ-grp} {X}
        u' : _
        u' = toGrpF u

        {- unit is its own inverse. -}
        p₁ : GrpTheory ⊢ (⋀ (u' ⁻) ≈ u')
        p₁ = begin ((u' ⁻))
                   ≈⟨  psym (psubst unitL-ax (λ x₁ → (u' ⁻)) ∼⟨⟩) ⟩
                   ((u' ∘ (u' ⁻)))
                   ≈⟨ psubst invL-ax (λ x₁ → u') ∼⟨⟩ ⟩
                   u'
                   ∎



    
