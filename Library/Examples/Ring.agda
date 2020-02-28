-- Universal Algebra Library
--
-- Rings extending Groups.
--
module Examples.Ring where

open import Algebra.Structures
open import Data.Bool
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Unit using (⊤;tt)
import Function as F
open import Function.Equality renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Level renaming (zero to lzero ; suc to lsuc)
open import Relation.Binary
import Relation.Binary.EqReasoning as EqR

open import Birkhoff
import Equational
open import HeterogeneousVec renaming (map to vmap)
open import Morphisms
open import Product
open import TermAlgebra
open import UnivAlgebra

open Hom

open import Examples.Monoid
open import Examples.Group

module SemiRing {op-semiring : List ⊤ × ⊤ → Set}
                (0#          : op-semiring ([] ↦ tt))
                (1#          : op-semiring ([] ↦ tt))
                (add         : op-semiring ((tt ∷ [ tt ]) ↦ tt))
                (mult        : op-semiring ((tt ∷ [ tt ]) ↦ tt))
       where

  Σ-sr : Signature
  Σ-sr = record { sorts = ⊤ ; ops = op-semiring }

  {- (R, +) is a abelian monoid with identity element 0:
     - (x + y) + z = x + (y + z)
     - 0 + x = x + 0 = x
     - x + y = y + x
  -}
  open module AM = AbeMonoid {op-semiring} 0# add
  {- (R, ⋅) is a monoid with identity element 1:
     - (x ⋅ y) ⋅ z = x ⋅ (y ⋅ z)
     - 1 ⋅ x = x ⋅ 1 = x
  -}
  open module M'  = Monoid   {op-semiring} 1# mult

  module SemiRingTheory where
    open AM.AbeTheory
    open M'.Theory  hiding (term)

    module SR = OpenTerm Σ-sr X renaming (T_〔_〕 to SRTerms)
    open SR
    open Equational Σ-sr


    Eq-sr : Set₁
    Eq-sr = Equation tt

    SRTerm : Set
    SRTerm = SRTerms ∥ tt ∥

    module SRSmartcons where
    -- smart constructors
      _⊹_ : SRTerm → SRTerm → SRTerm
      a ⊹ b = term add ⟨⟨ a , b ⟩⟩

      _⋆_ : SRTerm → SRTerm → SRTerm
      a ⋆ b = term mult ⟨⟨ a , b ⟩⟩

      x : Term
      x = term (inj₂ 0) ⟨⟩

      y : Term
      y = term (inj₂ 1) ⟨⟩

      z : Term
      z = term (inj₂ 2) ⟨⟩

      0' : SRTerm
      0' = term (inj₁ 0#) ⟨⟩

    open SRSmartcons
    {- Multiplication left and right distributes over addition:
       - x ⋅ (y + z) = (x ⋅ y) + (x ⋅ z)
       - (x + y) ⋅ z = (x ⋅ z) + (y ⋅ z)
    -}

    distMultOverAddLeft : Eq-sr
    distMultOverAddLeft = ⋀ X , x ⋆ (y ⊹ z) ≈ (x ⋆ y) ⊹ (x ⋆ z)

    distMultOverAddRight : Eq-sr
    distMultOverAddRight = ⋀ X , (x ⊹ y) ⋆ z ≈ (x ⋆ z) ⊹ (y ⋆ z)

    {- Multiplication by 0 annihilates R:
      - 0 ⋅ a = a ⋅ 0 = 0
    -}

    absMultLeft : Eq-sr
    absMultLeft = ⋀ X , 0' ⋆ x ≈ 0'

    absMultRight : Eq-sr
    absMultRight = ⋀ X , x ⋆ 0' ≈ 0'

    SRTheory : Theory (replicate 11 tt)
    SRTheory = distMultOverAddLeft ▹ distMultOverAddRight ▹
               absMultLeft ▹ absMultRight ▹
               MonTheory ++v AbeMonTheory

module Ring {op-ring : List ⊤ × ⊤ → Set}
            (0#      : op-ring ([] ↦ tt))
            (1#      : op-ring ([] ↦ tt))
            (minus   : op-ring ([ tt ] ↦ tt))
            (add     : op-ring ((tt ∷ [ tt ]) ↦ tt))
            (mult    : op-ring ((tt ∷ [ tt ]) ↦ tt))
       where

  Σ-ring : Signature
  Σ-ring = record { sorts = ⊤ ; ops = op-ring }

  {- (R, +) is an abelian group under addition with identity element 0:
    - (x + y) + z = x + (y + z)
    - x + y = y + x
    - 0 + x = x + 0 = x
    - a + (−a) = (−a) + a = 0
  -}
  open module AG = AbeGroup {op-ring} 0# minus add

  {- (R, ⋅) is a monoid under multiplication with identity element 1:
     - (x ⋅ y) ⋅ z = x ⋅ (y ⋅ z)
     - 1 ⋅ x = x ⋅ 1 = x
  -}
  open module M = Monoid {op-ring} 1# mult

  module RingTheory where
    open AG.AbeGrpTheory
    open M.Theory hiding (term)

    module RT = OpenTerm Σ-ring X renaming (T_〔_〕 to RTerms)
    open RT
    open Equational Σ-ring
    Eq-r : Set₁
    Eq-r = Equation tt

    -- A formula is a term of the Term Algebra
    Term-r : Set
    Term-r = RTerms ∥ tt ∥

    module SRSmartcons where
    -- smart constructors
      _⊹_ : Term-r → Term-r → Term-r
      a ⊹ b = term add ⟨⟨ a , b ⟩⟩

      _⋆_ : Term-r → Term-r → Term-r
      a ⋆ b = term mult ⟨⟨ a , b ⟩⟩

      x : Term-r
      x = term (inj₂ 0) ⟨⟩

      y : Term-r
      y = term (inj₂ 1) ⟨⟩

      z : Term-r
      z = term (inj₂ 2) ⟨⟩

    open SRSmartcons
    {- Multiplication left and right distributes over addition:
       - x ⋅ (y + z) = (x ⋅ y) + (x ⋅ z)
       - (x + y) ⋅ z = (x ⋅ z) + (y ⋅ z)
    -}

    distMultOverAddLeft : Eq-r
    distMultOverAddLeft = ⋀ X , x ⋆ (y ⊹ z) ≈ (x ⋆ y) ⊹ (x ⋆ z)

    distMultOverAddRight : Eq-r
    distMultOverAddRight = ⋀ X , (x ⊹ y) ⋆ z ≈ (x ⋆ z) ⊹ (y ⋆ z)

    RTheory : Theory (replicate 11 tt)
    RTheory = distMultOverAddLeft ▹ distMultOverAddRight ▹
              MonTheory ++v AbeGrpTheory


module CommutativeRing {op-cring : List ⊤ × ⊤ → Set}
                       (0#      : op-cring ([] ↦ tt))
                       (1#      : op-cring ([] ↦ tt))
                       (minus   : op-cring ([ tt ] ↦ tt))
                       (add     : op-cring ((tt ∷ [ tt ]) ↦ tt))
                       (mult    : op-cring ((tt ∷ [ tt ]) ↦ tt))
       where

  Σ-cring : Signature
  Σ-cring = record { sorts = ⊤ ; ops = op-cring }

  {- (R, 0, 1, -, +, *) is ring -}
  open module R = Ring {op-cring} 0# 1# minus add mult

  module CommRingTheory where
    open R.RingTheory

    X : Vars Σ-cring
    X ⊤ = ℕ

    module CR = OpenTerm Σ-cring X renaming (T_〔_〕 to CRTerms)
    open CR
    open Equational Σ-cring

    Eq-cr : Set₁
    Eq-cr = Equation tt

    open SRSmartcons
    {-  Multiplication is commutative:
       - x ⋅ y = y ⋅ x
    -}
    commMult : Eq-cr
    commMult = ⋀ X , x ⋆ y ≈ y ⋆ x

    CRTheory : Theory (replicate 12 tt)
    CRTheory = commMult ▹ RTheory
