module Examples.Monoid where


open import UnivAlgebra
open import Equational
open import AlgTransf
open import Data.Unit hiding (setoid)
open import Data.List
open import Data.Product
open import Data.Nat
open import Data.Sum
open import HeterogeneousVec
open import Setoids

open Signature
open Algebra
open Hom


data op-mon : List ⊤ × ⊤ → Set where
  e    : op-mon ([] ↦ tt)
  op   : op-mon ((tt ∷ [ tt ]) ↦ tt)


Σ-mon : Signature
Σ-mon = record { sorts = ⊤ ; ops = op-mon }

module Theory where

  X : Vars Σ-mon
  X ⊤ = ℕ

  Eq₁ : Set
  Eq₁ = Equation Σ-mon X tt

  open TermAlgebra

  
  -- A formula is a term of the Term Algebra
  Form : Set
  Form = HU (Σ-mon 〔 X 〕) tt


  module Smartcons where
    -- smart constructors
    _∘_ : Form → Form → Form
    φ ∘ ψ = term op ⟨⟨ φ , ψ ⟩⟩

    x : Form
    x = term (inj₂ 0) ⟨⟩
    
    y : Form
    y = term (inj₂ 1) ⟨⟩

    z : Form
    z = term (inj₂ 2) ⟨⟩

    u : Form
    u = term (inj₁ e) ⟨⟩

  open Smartcons
  -- Axioms
  assocOp : Eq₁
  assocOp = ⋀ (x ∘ y) ∘ z ≈ (x ∘ (y ∘ z))

  unitLeft : Eq₁
  unitLeft = ⋀ u ∘ x ≈ x

  unitRight : Eq₁
  unitRight = ⋀ x ∘ u ≈ x

  MonTheory : Theory Σ-mon X (tt ∷ tt ∷ [ tt ])
  MonTheory = assocOp ▹ (unitLeft ▹ unitRight ▹ ⟨⟩)


  module Monoids where
    open import Algebra.Structures
    open import Data.Bool
    open import Relation.Binary.Core as BC
    
    MkMonoid : ∀ {a l A _≈_ _∘_} {e : A} → (m : IsMonoid {a} {l} _≈_ _∘_ e) → Algebra {a} {l} Σ-mon 
    MkMonoid {A = A} {_≈_} {_∘_} {eA} isMon = (λ _ → record { Carrier = A ; _≈_ = _≈_
                                                       ; isEquivalence = isEquivalence  })
                                       ∥ (λ { e → record { _⟨$⟩_ = λ x₁ → eA ; cong = λ {i} {j} _ →
                                                                                          BC.IsEquivalence.refl
                                                                                          (IsSemigroup.isEquivalence (isSemigroup )) }
                                         ; op → record { _⟨$⟩_ = λ { (v ▹ v₁ ▹ ⟨⟩) → v ∘ v₁ }
                                         ; cong = λ { (∼▹ x₁ (∼▹ x₂ ∼⟨⟩)) → ∙-cong x₁ x₂ } } })
             where open IsMonoid isMon

    MonoidModel : ∀ {a l A _≈_ _∘_} {e : A} → (m : IsMonoid {a} {l} _≈_ _∘_ e) → MkMonoid m ⊨T MonTheory
    MonoidModel m here θ ∼⟨⟩ = IsSemigroup.assoc (isSemigroup m) (θ 0) (θ 1) (θ 2)
      where open IsMonoid
    MonoidModel m (there here) θ ∼⟨⟩ = proj₁ (identity m) (θ 0) 
      where open IsMonoid
    MonoidModel m (there (there here)) θ x₂ = proj₂ (identity m) (θ 0)
      where open IsMonoid
    MonoidModel m (there (there (there ()))) θ x₂


    


    
