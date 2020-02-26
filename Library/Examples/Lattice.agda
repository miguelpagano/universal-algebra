------------------------------------------------------------
-- Universal Algebra Library
--
-- Lattices as an equational theory.
------------------------------------------------------------

open import Data.List
open import Data.Unit hiding (setoid)
open import Examples.Monosorted
module Examples.Lattice (lattice-ops : ms-ops)
                        (∨-op ∧-op : lattice-ops binary) where


open import Data.Bool
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Sum
import Function as F
open import Function.Equality renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Level renaming (zero to lzero ; suc to lsuc)
open import Reflection
open import Relation.Binary
import Relation.Binary.EqReasoning as EqR


open import Birkhoff
import Equational
open import HeterogeneousVec renaming (map to vmap)
open import Morphisms
open import Product
open import Setoids hiding (∥_∥)
open import TermAlgebra using (Vars; module OpenTerm)
open import UnivAlgebra


open Hom

data lattice-ops' : ms-type → Set where
  meet-op join-op : lattice-ops' binary

Σ-lattice : Signature
Σ-lattice = record { sorts = ms-sorts ; ops = lattice-ops' }

module Theory where
  X : Vars Σ-lattice
  X ms-sort = ℕ

  open OpenTerm Σ-lattice X renaming (T_〔_〕 to Terms;var to v) public
  open Equational Σ-lattice

  Eq₁ : Set
  Eq₁ = Equation X ms-sort

  LTerm : Set
  LTerm = Terms ∥ ms-sort ∥

  x : LTerm
  x = term (inj₂ 0) ⟨⟩

  y : LTerm
  y = term (inj₂ 1) ⟨⟩

  z : LTerm
  z = term (inj₂ 2) ⟨⟩

  binary-smart : (op-name : Name) → (op : Name) → TC ⊤
  binary-smart op-name op = defineFun op-name
    [ clause
       ( arg (arg-info visible relevant) (var "x")
      ∷ arg (arg-info visible relevant) (var "y")
      ∷ []
      )
    (con (quote OpenTerm.term)
        (arg vis (con op [])
         ∷
        arg vis (
          con (quote _▹_) (
               arg vis (var 1 [])
            ∷ arg vis (con (quote _▹_)
                  (arg vis ((var 0 []))
                  ∷ arg vis (con (quote ⟨⟩) [])
                  ∷ []
                  ))
            ∷ []
            )
        )
        ∷
        []
         )
    )
    ]
    where
    vis = arg-info visible relevant



  _∧'_ _∨'_ : LTerm → LTerm → LTerm
  unquoteDef _∨'_ = binary-smart _∨'_ (quote meet-op)
  unquoteDef _∧'_ = binary-smart _∧'_ (quote join-op)

  ex : LTerm
  ex = x ∨' y

  assocOp : Eq₁
  assocOp = ⋀ (x ∨' y) ∨' z ≈ (x ∨' (y ∨' z))

{-
  module Theory where

    X : Vars Σ-mon
    X ⊤ = ℕ

    open OpenTerm Σ-mon X renaming (T_〔_〕 to Terms) public
    open Equational Σ-mon

    Eq₁ : Set
    Eq₁ = Equation X tt

    Term : Set
    Term = Terms ∥ tt ∥

    module MonSmartcons where
    -- smart constructors
      _∘_ : Term → Term → Term
      φ ∘ ψ = term ● ⟨⟨ φ , ψ ⟩⟩

      x : Term
      x = term (inj₂ 0) ⟨⟩

      y : Term
      y = term (inj₂ 1) ⟨⟩

      z : Term
      z = term (inj₂ 2) ⟨⟩

      u : Term
      u = term (inj₁ e) ⟨⟩

    open MonSmartcons
    -- Axioms
    assocOp : Eq₁
    assocOp = ⋀ (x ∘ y) ∘ z ≈ (x ∘ (y ∘ z))

    unitLeft : Eq₁
    unitLeft = ⋀ u ∘ x ≈ x

    unitRight : Eq₁
    unitRight = ⋀ x ∘ u ≈ x

    pattern mon-assoc-ax = here
    pattern mon-unitL-ax = there here
    pattern mon-unitR-ax  = there (there here)

    MonTheory  : Theory X _
    MonTheory = assocOp ▹ (unitLeft ▹ unitRight ▹ ⟨⟩)
-}
