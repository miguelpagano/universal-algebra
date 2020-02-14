{- Definition of the theory of Groups, extending theory of Monoids. -}
module Examples.Group where

open import UnivAlgebra
open import Equational
open import Morphisms
open import SigMorphism
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
  mop : ∀ {ar} {s} → (op-mon (ar ↦ s)) → op-grp (ar ↦ s)
  _⁻¹ : op-grp ([ tt ] ↦ tt)

Σ-grp : Signature
Σ-grp = record { sorts = ⊤ ; ops = op-grp }

module GrpTheory where
  open Theory
  -- Axioms

  Eq-grp : Set
  Eq-grp = Equation Σ-grp X tt

  open import TermAlgebra
  
  -- A formula is a term of the Term Algebra
  Form-grp : Set
  Form-grp = HU (Σ-grp 〔 X 〕) tt

  toGrpF : Form → Form-grp
  toGrpF (term {[]} {.tt} (inj₁ e) x₁) = term (inj₁ (mop e)) ⟨⟩
  toGrpF (term {[]} {.tt} (inj₂ y) x) = term (inj₂ y) ⟨⟩
  toGrpF (term {.tt ∷ .(tt ∷ [])} {.tt} op (v ▹ v₁ ▹ ⟨⟩)) =
               term (mop op) ((toGrpF v) ▹ ((toGrpF v₁) ▹ ⟨⟩))

  toGrpEq : Eq₁ → Eq-grp
  toGrpEq (⋀ left ≈ right if「 carty 」 (us , us')) =
    ⋀ (toGrpF left) ≈ (toGrpF right) if「 carty 」
                      (vmap (λ i x → toGrpF x) us , vmap (λ i x → toGrpF x) us')

  module GrpSmartcons where
    
    -- smart constructors
    _∘_ : Form-grp → Form-grp → Form-grp
    a ∘ b = term (mop op) ⟨⟨ a , b ⟩⟩

    _⁻ : Form-grp → Form-grp
    a ⁻ = term _⁻¹ (⟪ a ⟫)

    x : Form-grp
    x = term (inj₂ 0) ⟨⟩

    u : Form-grp
    u = term (inj₁ (mop e)) ⟨⟩

  open GrpSmartcons
  -- Axioms
  invElemLeft : Eq-grp
  invElemLeft = ⋀ (x ∘ (x ⁻)) ≈ u

  invElemRight : Eq-grp
  invElemRight = ⋀ ((x ⁻) ∘ x) ≈ u

  MonTheory' : _
  MonTheory' = vmap (λ _ eq → toGrpEq eq) MonTheory

  GrpTheory : Theory Σ-grp X (tt ∷ tt ∷ tt ∷ tt ∷ [ tt ])
  GrpTheory = invElemRight ▹ (invElemLeft ▹ MonTheory')

  module Props where
    open import Relation.Binary.EqReasoning (⊢RSetoid GrpTheory tt)
    open Subst {Σ-grp} {X}

    pattern invR-ax = here
    pattern invL-ax = there here
    pattern ass-ax  = there (there here)
    pattern unitL-ax = there (there (there here ))
    pattern unitR-ax = there (there (there (there here)))

    {- unit is its own inverse. -}
    p₁ : GrpTheory ⊢ (⋀ (u ⁻) ≈ u)
    p₁ = begin ((u ⁻))
         ≈⟨  psym (psubst unitL-ax (λ x₁ → (u ⁻)) ∼⟨⟩) ⟩
         ((u ∘ (u ⁻)))
         ≈⟨ psubst invL-ax (λ x₁ → u) ∼⟨⟩ ⟩
         u
         ∎

    inv-inv : GrpTheory ⊢ (⋀ x ≈ ((x ⁻) ⁻) if「 [] 」 (⟨⟩ , ⟨⟩))
    inv-inv = begin x
              ≈⟨ psym (psubst unitR-ax (λ x → term (inj₂ x) ⟨⟩) ∼⟨⟩) ⟩
              (x ∘ u)
              ≈⟨ preemp (∼▹ prefl (∼▹ (psym (psubst invL-ax
                                                (λ _ → x ⁻) ∼⟨⟩)) ∼⟨⟩)) ⟩
              (x ∘ ((x ⁻) ∘ (((x ⁻)) ⁻)))
              ≈⟨ psym (psubst ass-ax σ ∼⟨⟩) ⟩
              ((x ∘ (x ⁻)) ∘ ((x ⁻) ⁻))
              ≈⟨ preemp (∼▹ (psubst invL-ax (λ _ → x) ∼⟨⟩) (∼▹ prefl ∼⟨⟩)) ⟩
              (u ∘ ((x ⁻) ⁻))
              ≈⟨ psubst unitL-ax (λ _ → (x ⁻) ⁻) ∼⟨⟩ ⟩
              ((x ⁻) ⁻)
              ∎
              where σ : Subst
                    σ zero = x
                    σ (suc zero) = x ⁻
                    σ (suc (suc zero)) = (x ⁻) ⁻
                    σ v = term (inj₂ v) ⟨⟩
    
module AbeGrpTheory where
  open Theory
  open GrpTheory

  Eq-abe-grp : Set
  Eq-abe-grp = Eq-grp

  open import TermAlgebra

  Form-abe-grp : Set
  Form-abe-grp = Form-grp

  module AbeGrpSmartcons where
    
    y : Form-grp
    y = term (inj₂ 1) ⟨⟩

  open GrpSmartcons
  open AbeGrpSmartcons
  -- Commutativity
  commOp : Eq-abe-grp
  commOp = ⋀ (x ∘ y) ≈ (y ∘ x)

  AbeGrpTheory : Theory Σ-grp X (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [ tt ])
  AbeGrpTheory = commOp ▹ GrpTheory
