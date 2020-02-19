-- Universal Algebra Library
--
-- Fields do not have a finite equational theory.
--
module Examples.Field where

open import Algebra
open import Data.Bool
open import Data.Bool.Properties
open import Data.Empty
open import Data.List
open import Data.Product
open import Data.Unit hiding (setoid)
import Function as F
open import Function.Equality renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Level renaming (zero to lzero ; suc to lsuc)
open import Relation.Binary hiding (Total)
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PropositionalEquality as PE hiding ([_])
open import Relation.Nullary using (¬_)

open import Birkhoff
open import Equational
open import HeterogeneousVec
open import Product
open import Setoids
open import UnivAlgebra

open Signature
open UnivAlgebra.Algebra

record _⇔_ {l₀} {l₁} (A : Set l₀) (B : Set l₁) : Set (l₀ ⊔ l₁) where
  field
    to   : A → B
    from : B → A


-- As in the stdlib.
module _ {a ℓ} {A : Set a}
               (_≈_ : Rel A ℓ) where

  NonZeroMultInverse : A → A → Op₂ A → Op₁ A → Set _
  NonZeroMultInverse zero e _∙_ _⁻¹ = ∀ x → ¬ (x ≈ zero) → (x ∙ (x ⁻¹)) ≈ e

  record IsField 
               (_+_ _*_ : Op₂ A) (- _⁻¹ : Op₁ A) (0# 1# : A) : Set ? where
    field
      isCommRing   : IsCommutativeRing (_≈_)
                                       _+_
                                       _*_
                                       -
                                       0#
                                       1#
      nonzero-unit : NonZeroMultInverse 0# 1# _*_ _⁻¹

    nonzero-unitL-ax : ∀ x → ¬ (x ≈ 0#) → ((x ⁻¹) * x) ≈ 1#
    nonzero-unitL-ax x x≉0 = begin
                     (x ⁻¹) * x     ≈⟨ *-comm (x ⁻¹) x ⟩
                     x * (x ⁻¹)     ≈⟨ nonzero-unit x x≉0 ⟩
                     1# ∎
      where open IsCommutativeRing isCommRing
            open EqR setoid

module Fields where

  data op-field : List ⊤ × ⊤ → Set where
       0#       : op-field ([] ↦ tt)
       1#       : op-field ([] ↦ tt)
       ─_       : op-field ([ tt ] ↦ tt)
       _⁻¹      : op-field ([ tt ] ↦ tt)
       _⊹_      : op-field ((tt ∷ [ tt ]) ↦ tt)
       _⋆_      : op-field ((tt ∷ [ tt ]) ↦ tt)

  Σ-field : Signature
  Σ-field = record { sorts = ⊤ ; ops = op-field }

  open Universe
  open Setoid

  UnivCarrier : Universe Σ-field lzero lzero
  UnivCarrier _ = PE.setoid Bool

  OpSem : {ar : List ⊤} {s : ⊤} → op-field (ar ↦ s) →
          (UnivCarrier ✳ ar) ⟶ UnivCarrier s
  OpSem {.[]} {.tt} 0# = record { _⟨$⟩_ = λ _ → false
                                ; cong = λ _ → PE.refl
                                }
  OpSem {.[]} {.tt} 1# = record { _⟨$⟩_ = λ _ → true
                                ; cong = λ _ → PE.refl
                                }
  OpSem {.(tt ∷ [])} {.tt} ─_ =
        record { _⟨$⟩_ = λ { ⟪ b ⟫ → b }
               ; cong = λ { (∼▹ b₀≡b₁ ∼⟨⟩) → b₀≡b₁ }
               }
  OpSem {.(tt ∷ [])} {.tt} _⁻¹ =
        record { _⟨$⟩_ = λ { ⟪ b ⟫ → b }
               ; cong = λ { (∼▹ b₀≡b₁ ∼⟨⟩) → b₀≡b₁ }
               }
  OpSem {.(tt ∷ tt ∷ [])} {.tt} _⊹_ =
        record { _⟨$⟩_ = λ { ⟨⟨ b₀ , b₁ ⟩⟩ → b₀ xor b₁ }
               ; cong = λ { (∼▹ b₀≡b₁ (∼▹ b₀≡b₁' ∼⟨⟩)) →
                            PE.cong₂ _xor_ b₀≡b₁ b₀≡b₁'
                          }
               }
  OpSem {.(tt ∷ tt ∷ [])} {.tt} _⋆_ =
        record { _⟨$⟩_ = λ { ⟨⟨ b₀ , b₁ ⟩⟩ → b₀ ∧ b₁ }
               ; cong = λ { (∼▹ b₀≡b₁ (∼▹ b₀≡b₁' ∼⟨⟩)) →
                            PE.cong₂ _∧_ b₀≡b₁ b₀≡b₁'
                          }
               }

  GF2 : Algebra {lzero} {lzero} Σ-field
  GF2 = record
    { _⟦_⟧ₛ = UnivCarrier
    ; _⟦_⟧ₒ = OpSem
    }



  GF2-is-field : IsField {A = Bool} PE._≡_ _xor_ _∧_ F.id F.id false true
  GF2-is-field = record
    { isCommRing = isCommutativeRing xor-∧-commutativeRing
    ; nonzero-unit = gf2nunit
    }
    where
    open CommutativeRing
    gf2nunit : NonZeroMultInverse PE._≡_ false true _∧_ F.id
    gf2nunit false x≢0 = ⊥-elim (x≢0 PE.refl)
    gf2nunit true x≢0 = PE.refl


  open ProdAlg
  open IsField

  GF2² : Algebra {lzero} {lzero} Σ-field
  GF2² = GF2 ×-alg GF2

  -- GF2² is not a field because there is an nonzero element that lacks
  -- an multiplicative inverse.
  GF2²-isnot-field : ¬ IsField GF2²
  GF2²-isnot-field A = not-¬ (proj₁ (nonzero-unit A p p≢0)) PE.refl
    where
    _≈GF2²_ : Rel (Bool × Bool) lzero
    _≈GF2²_ = _≈_ (GF2² ⟦ tt ⟧ₛ)

    p : Bool × Bool
    p = (false , true)

    p≢0 : ¬ p ≈GF2² ((GF2² ⟦ 0# ⟧ₒ) ⟨$⟩ ⟨⟩)
    p≢0 ()

  open ModSemiEquationIsISP

  -- We assume that there is an equational theory for fields; ie. a
  -- theory whose models are exactly fields in the external sense.
  FieldIsNotEquational : ¬ (Σ[ ar ∈ List (sorts Σ-field) ]
                            (Σ[ X ∈ Vars Σ-field ]
                            (Σ[ T ∈ Theory Σ-field X ar ]
                               ∀ (F : Algebra {lzero} {lzero} Σ-field) →
                                      (F ⊨T T) ⇔ (IsField F))))
  FieldIsNotEquational (ar , X , T , p) = GF2²-isnot-field GF2²-is-field
    where
    open _⇔_
    pGF2-From : IsField GF2 → GF2 ⊨T T
    pGF2-From = from (p GF2)

    GF2⊨TT : GF2 ⊨T T
    GF2⊨TT = pGF2-From GF2-is-field

    -- Since GF2 is a model and models of equational theories are closed
    -- under binary products, GF2² is also a model.
    GF2²⊨TT : GF2² ⊨T T
    GF2²⊨TT = binProdClosed T GF2 GF2 GF2⊨TT GF2⊨TT
    GF2²-is-field : IsField GF2²
    GF2²-is-field = to (p GF2²) GF2²⊨TT
