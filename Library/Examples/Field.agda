module Examples.Field where

open import UnivAlgebra
open import Equational
open import Data.Unit hiding (setoid)
open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open import Data.Bool.Properties
open import Data.Product
open import HeterogeneousVec
open import Setoids
open import Level renaming (zero to lzero ; suc to lsuc)
open import Function.Equality renaming (_∘_ to _∘ₛ_) hiding (setoid)

open Signature
open Algebra

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

  UnivCarrier : Universe Σ-field lzero lzero
  UnivCarrier _ = setoid Bool

  OpSem : {ar : List ⊤} {s : ⊤} → op-field (ar ↦ s) →
          (UnivCarrier ✳ ar) ⟶ UnivCarrier s
  OpSem {.[]} {.tt} 0# = record { _⟨$⟩_ = λ _ → false
                                ; cong = λ _ → refl
                                }
  OpSem {.[]} {.tt} 1# = record { _⟨$⟩_ = λ _ → true
                                ; cong = λ _ → refl
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
                            cong₂ _xor_ b₀≡b₁ b₀≡b₁'
                          }
               }
  OpSem {.(tt ∷ tt ∷ [])} {.tt} _⋆_ =
        record { _⟨$⟩_ = λ { ⟨⟨ b₀ , b₁ ⟩⟩ → b₀ ∧ b₁ }
               ; cong = λ { (∼▹ b₀≡b₁ (∼▹ b₀≡b₁' ∼⟨⟩)) →
                            cong₂ _∧_ b₀≡b₁ b₀≡b₁'
                          }
               }

  GF2 : Algebra {lzero} {lzero} Σ-field
  GF2 = record { _⟦_⟧ₛ = UnivCarrier
               ; _⟦_⟧ₒ = OpSem
               }

  open import Relation.Nullary using (¬_)
  open import Algebra.Structures
  open import Algebra.Definitions
  open import Relation.Binary hiding (Total)
  open Setoid
  open import Function.Equality
  open import Data.Unit
  open import Data.Empty
  import Relation.Binary.PropositionalEquality as PE
  
  record _⇔_ {l₀} {l₁} (A : Set l₀) (B : Set l₁) : Set (l₀ ⊔ l₁) where
    field
      to   : A → B
      from : B → A

  nonzero-unit-ax : ∀ {l₀} {l₁} →
                    (A : Algebra {l₀} {l₁} Σ-field) → Set (l₀ ⊔ l₁)
  nonzero-unit-ax {l₀} {l₁} A = ∀ x → ¬ (x ≈A 0') → nonzero-unitL-ax x
                                                     ×
                                                     nonzero-unitR-ax x
       where
         CA : Set l₀
         CA = Carrier (A ⟦ tt ⟧ₛ)
         1' : CA
         1' = A ⟦ 1# ⟧ₒ ⟨$⟩ ⟨⟩
         0' : CA
         0' = A ⟦ 0# ⟧ₒ ⟨$⟩ ⟨⟩
         _⋆'_ : CA → CA → CA
         x ⋆' y = A ⟦ _⋆_ ⟧ₒ ⟨$⟩ ⟨⟨ x , y ⟩⟩
         _⁻¹' : CA → CA
         x ⁻¹' = A ⟦ _⁻¹ ⟧ₒ ⟨$⟩ ⟪ x ⟫
         _≈A_ : CA → CA → Set l₁
         _≈A_ = _≈_ (A ⟦ tt ⟧ₛ)

         nonzero-unitR-ax : CA → Set l₁
         nonzero-unitR-ax x = (x ⋆' (x ⁻¹')) ≈A 1'
         nonzero-unitL-ax : CA → Set l₁
         nonzero-unitL-ax x = ((x ⁻¹') ⋆' x) ≈A 1'
         
  
  record IsField {l₀} {l₁} (A : Algebra {l₀} {l₁} Σ-field) : Set (l₀ ⊔ l₁) where
      field
        isCommRing   : IsCommutativeRing (_≈_ (A ⟦ tt ⟧ₛ))
                                         (λ x y → A ⟦ _⊹_ ⟧ₒ ⟨$⟩ ⟨⟨ x , y ⟩⟩)
                                         (λ x y → A ⟦ _⋆_ ⟧ₒ ⟨$⟩ ⟨⟨ x , y ⟩⟩ )
                                         (λ x → (A ⟦ ─_ ⟧ₒ) ⟨$⟩ ⟪ x ⟫)
                                         (A ⟦ 0# ⟧ₒ ⟨$⟩ ⟨⟩)
                                         (A ⟦ 1# ⟧ₒ ⟨$⟩ ⟨⟩)
        nonzero-unit : nonzero-unit-ax A

  GF2-is-field : IsField GF2
  GF2-is-field = record { isCommRing = isCommutativeRing xor-∧-commutativeRing
                        ; nonzero-unit = gf2nunit
                        }
               where gf2nunit : nonzero-unit-ax GF2
                     gf2nunit false x≢0 = ⊥-elim (x≢0 PE.refl)
                     gf2nunit true x≢0 = (PE.refl , PE.refl)
                     open import Algebra.Bundles as AB
                     open AB.CommutativeRing
                     
  open import Product
  open ProdAlg
  open IsField
  
  GF2² : Algebra {lzero} {lzero} Σ-field
  GF2² = GF2 ×-alg GF2

  GF2²-isnot-field : ¬ IsField GF2²
  GF2²-isnot-field A = not-¬ ( proj₁ (proj₁ (nonzero-unit A p p≢0))) PE.refl
    where
      _≈GF2²_ : Rel (Bool × Bool) lzero
      _≈GF2²_ = _≈_ (GF2² ⟦ tt ⟧ₛ)

      p : Bool × Bool
      p = (false , true)

      p≢0 : ¬ p ≈GF2² ((GF2² ⟦ 0# ⟧ₒ) ⟨$⟩ ⟨⟩)
      p≢0 ()

  open import Birkhoff
  open ModSemiEquationIsISP

  FieldIsNotEquational : ∀ {X ar} → ¬ (Σ[ T ∈ Theory Σ-field X ar ]
                                       ∀ (F : Algebra {lzero} {lzero} Σ-field) →
                                         (F ⊨T T) ⇔ (IsField F))
  FieldIsNotEquational (T , p) = GF2²-isnot-field GF2²-is-field
    where
      open _⇔_
      pGF2-From : IsField GF2 → GF2 ⊨T T
      pGF2-From = from (p GF2)

      GF2⊨TT : GF2 ⊨T T
      GF2⊨TT = pGF2-From GF2-is-field
      
      GF2²⊨TT : GF2² ⊨T T
      GF2²⊨TT = binProdClosed T GF2 GF2 GF2⊨TT GF2⊨TT
      GF2²-is-field : IsField GF2²
      GF2²-is-field = to (p GF2²) GF2²⊨TT 
