-------------------------------------------------------------
-- Universal Algebra Library
--
-- Conveniences for declaring monosorted equational theories.
-------------------------------------------------------------

module Examples.Monosorted where
open import Level renaming (suc to sucℓ) using (0ℓ)
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Reflection

import Equational
open import TermAlgebra
open import HeterogeneousVec
open import UnivAlgebra

ms-sorts : Set
ms-sorts = ⊤

ms-sort : ms-sorts
ms-sort = tt

ms-type : Set
ms-type = List ms-sorts × ms-sorts

ms-ops : Set (sucℓ 0ℓ)
ms-ops = ms-type → Set

n-ary : ℕ → ms-type
n-ary n = replicate n tt , tt

constant : ms-type
constant = n-ary 0

unary : ms-type
unary = n-ary 1

binary : ms-type
binary = n-ary 2

ternary : ms-type
ternary = n-ary 3

module _ where
  ⟨⟩' : Term
  ⟨⟩' = con (quote ⟨⟩) []
  _▹'_ : Term → Term → Term
  x ▹' xs = con (quote _▹_) (vArg x ∷ vArg xs ∷ [])

  unary-smart : (op-name : Name) → (op : Term) → TC ⊤
  unary-smart op-name op = defineFun op-name
    [ clause
      [ vArg (var "x") ]
      (con (quote OpenTerm.term)
        (vArg op
         ∷
         [ vArg (var 0 [] ▹' ⟨⟩') ]
        )
      )
    ]


  binary-smart : (op-name : Name) → (op : Term) → TC ⊤
  binary-smart op-name op = defineFun op-name
    [ clause
       ( vArg (var "x")
      ∷ vArg (var "y")
      ∷ []
      )
    (con (quote OpenTerm.term)
        (vArg op
         ∷
         vArg ((var 1 []) ▹' ((var 0 []) ▹' ⟨⟩'))
        ∷
        []
         )
    )
    ]

module EqTheory (ops : ms-type → Set) where

  Σ-ms : Signature
  Σ-ms = record { sorts = ms-sorts ; ops = ops }

  X : Vars Σ-ms
  X ms-sort = ℕ

  open Equational Σ-ms public
  open OpenTerm Σ-ms X renaming (T_〔_〕 to Terms;var to v) public

  Eq : Set₁
  Eq = Equation ms-sort

  ms-Term : Set
  ms-Term = Terms ∥ tt ∥

  𝓿u : ms-Term
  𝓿u = v 0

  𝓿x : ms-Term
  𝓿x = v 1

  𝓿y : ms-Term
  𝓿y = v 2

  𝓿z : ms-Term
  𝓿z = v 3

  assoc-op : (name : Name) → (op : Name) → (X' x y z : Name) → TC ⊤
  assoc-op na op X' x y z = defineFun na
    [ clause []
    (def (quote ⋀_,_≈_)
        (
        vArg (var 2 [])
        ∷
        vArg (def X' [])
        ∷
        vArg (x' ⊚ (y' ⊚ z'))
        ∷
        vArg ((x' ⊚ y') ⊚ z')
        ∷
        []
        )
    )
    ]
      where
      x' y' z' : Term
      x' = def x []
      y' = def y []
      z' = def z []
      _⊚_ : Term → Term → Term
      a ⊚ b = def op (vArg a ∷ vArg b ∷ [])

  comm-op : (name : Name) → (op : Name) → (X' x y : Name) → TC ⊤
  comm-op na op X' x y = defineFun na
    [ clause []
    (def (quote ⋀_,_≈_)
        (
        vArg (var 2 [])
        ∷
        vArg (def X' [])
        ∷
        vArg (x' ⊚ y')
        ∷
        vArg (y' ⊚ x')
        ∷
        []
        )
    )
    ]
      where
      x' y' : Term
      x' = def x []
      y' = def y []
      _⊚_ : Term → Term → Term
      a ⊚ b = def op (vArg a ∷ vArg b ∷ [])

  idemp-op : (name : Name) → (op : Name) → (X' x : Name) → TC ⊤
  idemp-op na op X' x = defineFun na
    [ clause []
    (def (quote ⋀_,_≈_)
        (
        vArg (var 2 [])
        ∷
        vArg (def X' [])
        ∷
        vArg (x' ⊚ x')
        ∷
        vArg x'
        ∷
        []
        )
    )
    ]
      where
      x' : Term
      x' = def x []
      _⊚_ : Term → Term → Term
      a ⊚ b = def op (vArg a ∷ vArg b ∷ [])

  absorption-op : (name : Name) → (op op' : Name) → (X' x y : Name) → TC ⊤
  absorption-op na op op' X' x y = defineFun na
    [ clause []
    (def (quote ⋀_,_≈_)
        (
        vArg (var 2 [])
        ∷
        vArg (def X' [])
        ∷
        vArg (x' ⊚ (x' ⊕ y'))
        ∷
        vArg x'
        ∷
        []
        )
    )
    ]
      where
      x' y' : Term
      x' = def x []
      y' = def y []
      _⊚_ _⊕_ : Term → Term → Term
      a ⊚ b = def op (vArg a ∷ vArg b ∷ [])
      a ⊕ b = def op' (vArg a ∷ vArg b ∷ [])
