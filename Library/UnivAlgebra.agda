-- Universal Algebra Library
--
-- Basic definitions of Heterogeneous Universal Algebra:
--   Signature, Algebra, Homomorphism, Congruence, Quotient, Subalgebra.
--
module UnivAlgebra where

open import Data.List.Base hiding (map)
open import Data.Product hiding (map)
open import Function
open import Function.Equality as FE hiding (setoid;id)
open import Level renaming (suc to lsuc ; zero to lzero)
open import Relation.Binary hiding (Total)
open import Relation.Binary.Indexed.Homogeneous
  hiding (Rel;Reflexive;Symmetric;Transitive)
open import Relation.Unary hiding (_⊆_;_⇒_)
open import Relation.Unary.Indexed using (IPred)

open import HeterogeneousVec
open import Setoids as S hiding (∥_∥)

pattern _↦_ ar s = (ar , s)

open Setoid

{- Multisort Signature -}
record Signature : Set₁ where
  field
    sorts  : Set
    ops    : (List sorts) × sorts → Set

  Arity : Set
  Arity = List sorts

  Type : Set
  Type = List sorts × sorts

open Signature public

module Universe (Σ : Signature) where
  Universe : ∀  ℓ₁ ℓ₂ → Set _
  Universe ℓ₁ ℓ₂ = (s : sorts Σ) → Setoid ℓ₁ ℓ₂

  _⟶ₛ_ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} →
         (X : Universe ℓ₁ ℓ₂) → (Y : Universe ℓ₃ ℓ₄) → Set _
  X ⟶ₛ Y = (s : sorts Σ) → X s ⟶ Y s
  -- a ≈X_s a' ⇒ f a ≈Y_s f a'

open Universe

-- Algebra
record Algebra {ℓ₁ ℓ₂ : Level} (Σ : Signature) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    _⟦_⟧ₛ : Universe Σ ℓ₁ ℓ₂
    -- ar : List (sorts Σ)
    -- s  : sorts Σ
    -- ⟦ s₁⟧ × … × ⟦ s_n ⟧
    -- ⟦ s ⟧
    _⟦_⟧ₒ : ∀ {ar s} → (f : ops Σ (ar , s)) → _⟦_⟧ₛ ✳ ar ⟶ _⟦_⟧ₛ s

  _∥_∥* : (ar : Arity Σ) → Set _
  _∥_∥* ar = S.∥ _⟦_⟧ₛ ✳ ar ∥

  _∥_∥ : ∀ s → Set _
  _∥_∥ s =  S.∥ _⟦_⟧ₛ s ∥

  ARel : (ℓ : Level) → Set (ℓ₁ ⊔ lsuc ℓ)
  ARel ℓ = IRel _∥_∥ ℓ

open Algebra public
-- A class of algebras is a predicate over algebras.
AlgClass : ∀ {ℓ₀ ℓ₁} Σ → Set (lsuc ℓ₀ ⊔ lsuc ℓ₁)
AlgClass {ℓ₀} {ℓ₁} Σ = Pred (Algebra {ℓ₀} {ℓ₁} Σ) (ℓ₀ ⊔ ℓ₁)

{- Subalgebras -}
open SetoidPredicate

OpClosed : ∀ {ℓ₁ ℓ₂ ℓ₃ Σ} → (A : Algebra {ℓ₁} {ℓ₂} Σ) →
           (P : IPred (A ∥_∥) ℓ₃) → Set _
OpClosed {ℓ₃ = ℓ₃} {Σ = Σ} A P =
  ∀ {ar s} (f : ops Σ (ar , s)) → (P ⇨v ⟨→⟩ P {s}) (A ⟦ f ⟧ₒ ⟨$⟩_)

-- Subalgebra condition: A subsetoid closed by operations.
record SubAlg {ℓ₃ ℓ₁ ℓ₂ Σ} (A : Algebra {ℓ₁} {ℓ₂} Σ) : Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃))
  where
  field
    pr   : (s : sorts Σ) → SetoidPredicate {ℓ₃ = ℓ₃} (A ⟦ s ⟧ₛ)
    opClosed : OpClosed {Σ = Σ} A (λ {s} → predicate (pr s))

  pcong : ∀ {ar} {v₁ v₂ : HVec (λ s → Carrier $ SubSetoid (A ⟦ s ⟧ₛ)
                                                 (predicate (pr s))) ar} →
            _∼v_ {l₁ = ℓ₂} {R = λ {s} → _≈_ (A ⟦ s ⟧ₛ) on proj₁} v₁ v₂ →
            _∼v_ {l₁ = ℓ₂} {R = λ {s} → _≈_ (A ⟦ s ⟧ₛ) }
                           (map (λ _ → proj₁) v₁)
                           (map (λ _ → proj₁) v₂)
  pcong = fmap∼v id

-- A subsetoid closed by operations is an Algebra.
SubAlgebra : ∀ {Σ} {ℓ₁ ℓ₂ ℓ₃} {A : Algebra {ℓ₁} {ℓ₂} Σ} →
                   SubAlg {ℓ₃ = ℓ₃} A → Algebra Σ
SubAlgebra {Σ} {A = A} S = record
  { _⟦_⟧ₛ = is
  ; _⟦_⟧ₒ = if
  }
  where
  open SubAlg S
  is : sorts Σ → _
  is s = SubSetoid (A ⟦ s ⟧ₛ) (predicate (pr s))
  if : ∀ {ar} {s} → (f : ops Σ (ar , s)) → is ✳ ar ⟶ is s
  if {ar} {s} f = record
    { _⟨$⟩_ = λ v → A ⟦ f ⟧ₒ ⟨$⟩ map (λ _ → proj₁) v , opClosed f (⇨₂ v)
    ; cong = λ { {v₁} {v₂} eq → Π.cong (A ⟦ f ⟧ₒ) (pcong eq) }
    }


{- Congruence -}
record Congruence {ℓ₃ ℓ₁ ℓ₂} {Σ : Signature}
                  (A : Algebra {ℓ₁} {ℓ₂} Σ) : Set (lsuc ℓ₃ ⊔ ℓ₂ ⊔ ℓ₁) where
  field
    -- the relation
    rel : IRel (A ∥_∥) ℓ₃
    -- should respect the underlying equality
    welldef : (s : sorts Σ) → WellDefRel (A ⟦ s ⟧ₛ) (rel {s})
    -- be an equivalence relation
    cequiv : (s : sorts Σ) → IsEquivalence (rel {s})
    -- and be closed under each operation
    csubst : ∀ {ar s} (f : ops Σ (ar , s)) → rel * =[ A ⟦ f ⟧ₒ ⟨$⟩_ ]⇒ rel {s}

open Congruence

_⊆_ : ∀ {ℓ₃ ℓ₁ ℓ₂ Σ} {A : Algebra {ℓ₁} {ℓ₂} Σ} → Rel (Congruence {ℓ₃} A) _
Φ ⊆ Ψ = ∀ s → rel Φ {s} ⇒ rel Ψ {s}


{- Quotient Algebra -}
infixl 10 _/_
_/_ : ∀ {ℓ₁ ℓ₂ ℓ₃ Σ} → (A : Algebra {ℓ₁} {ℓ₂} Σ) → (C : Congruence {ℓ₃} A) →
      Algebra {ℓ₁} {ℓ₃} Σ
A / φ = record
  { _⟦_⟧ₛ = A/φₛ
  ; _⟦_⟧ₒ = A/φₒ
  }
  where
  A/φₛ : _ → _
  A/φₛ s = record
    { Carrier = Carrier (A ⟦ s ⟧ₛ)
    ; _≈_ = rel φ {s}
    ; isEquivalence = cequiv φ s
    }
  A/φₒ : ∀ {ar} {s} → _ → (A/φₛ  ✳ ar) ⟶ A/φₛ s
  A/φₒ {ar} {s} f = record
    { _⟨$⟩_ = A ⟦ f ⟧ₒ ⟨$⟩_
    ; cong = csubst φ f
    }



