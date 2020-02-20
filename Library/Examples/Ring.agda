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
open import Equational
open import HeterogeneousVec renaming (map to vmap)
open import Morphisms
open import Product
open import Setoids
open import TermAlgebra
open import UnivAlgebra

open import UnivAlgebra
open import Equational
open import Morphisms
open import SigMorphism
open import Data.Unit hiding (setoid)
open import Data.List
open import Data.Product
open import Data.Nat
open import Data.Sum
open import HeterogeneousVec
open import Setoids

open Signature
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
    open M'.Theory

    open import TermAlgebra

    Eq-sr : Set
    Eq-sr = Equation Σ-sr X tt

    -- A formula is a term of the Term Algebra
    Form-sr : Set
    Form-sr = HU (Σ-sr 〔 X 〕) tt

    module SRSmartcons where
    -- smart constructors
      _⊹_ : Form-sr → Form-sr → Form-sr
      a ⊹ b = term add ⟨⟨ a , b ⟩⟩

      _⋆_ : Form-sr → Form-sr → Form-sr
      a ⋆ b = term mult ⟨⟨ a , b ⟩⟩

      x : Form
      x = term (inj₂ 0) ⟨⟩

      y : Form
      y = term (inj₂ 1) ⟨⟩

      z : Form
      z = term (inj₂ 2) ⟨⟩

      0' : Form-sr
      0' = term (inj₁ 0#) ⟨⟩

    open SRSmartcons
    {- Multiplication left and right distributes over addition:
       - x ⋅ (y + z) = (x ⋅ y) + (x ⋅ z)
       - (x + y) ⋅ z = (x ⋅ z) + (y ⋅ z)
    -}

    distMultOverAddLeft : Eq-sr
    distMultOverAddLeft = ⋀ x ⋆ (y ⊹ z) ≈ (x ⋆ y) ⊹ (x ⋆ z)

    distMultOverAddRight : Eq-sr
    distMultOverAddRight = ⋀ (x ⊹ y) ⋆ z ≈ (x ⋆ z) ⊹ (y ⋆ z)

    {- Multiplication by 0 annihilates R:
      - 0 ⋅ a = a ⋅ 0 = 0
    -}

    absMultLeft : Eq-sr
    absMultLeft = ⋀ 0' ⋆ x ≈ 0'

    absMultRight : Eq-sr
    absMultRight = ⋀ x ⋆ 0' ≈ 0'

    SRTheory : Theory Σ-sr X (replicate 11 tt)
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
    open M.Theory

    open import TermAlgebra

    Eq-r : Set
    Eq-r = Equation Σ-ring X tt

    -- A formula is a term of the Term Algebra
    Form-r : Set
    Form-r = HU (Σ-ring 〔 X 〕) tt

    module SRSmartcons where
    -- smart constructors
      _⊹_ : Form-r → Form-r → Form-r
      a ⊹ b = term add ⟨⟨ a , b ⟩⟩

      _⋆_ : Form-r → Form-r → Form-r
      a ⋆ b = term mult ⟨⟨ a , b ⟩⟩

      x : Form-r
      x = term (inj₂ 0) ⟨⟩

      y : Form-r
      y = term (inj₂ 1) ⟨⟩

      z : Form-r
      z = term (inj₂ 2) ⟨⟩

    open SRSmartcons
    {- Multiplication left and right distributes over addition:
       - x ⋅ (y + z) = (x ⋅ y) + (x ⋅ z)
       - (x + y) ⋅ z = (x ⋅ z) + (y ⋅ z)
    -}

    distMultOverAddLeft : Eq-r
    distMultOverAddLeft = ⋀ x ⋆ (y ⊹ z) ≈ (x ⋆ y) ⊹ (x ⋆ z)

    distMultOverAddRight : Eq-r
    distMultOverAddRight = ⋀ (x ⊹ y) ⋆ z ≈ (x ⋆ z) ⊹ (y ⋆ z)

    RTheory : Theory Σ-ring X (replicate 11 tt)
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
    open import TermAlgebra

    X : Vars Σ-cring
    X ⊤ = ℕ

    Eq-cr : Set
    Eq-cr = Equation Σ-cring X tt

    open SRSmartcons
    {-  Multiplication is commutative:
       - x ⋅ y = y ⋅ x
    -}
    commMult : Eq-cr
    commMult = ⋀ x ⋆ y ≈ y ⋆ x

    CRTheory : Theory Σ-cring X (replicate 12 tt)
    CRTheory = commMult ▹ RTheory
