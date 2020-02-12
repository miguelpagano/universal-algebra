{- Basic definitions of Heterogeneous Universal Algebra: 
   Signature, Algebra, Homomorphism, Congruence, Quotient, Subalgebra. -}

module UnivAlgebra where

open import Relation.Binary hiding (Total)
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Nat renaming (_⊔_ to _⊔ₙ_)
open import Data.Product renaming (map to pmap)
open import Function as F
open import Function.Equality as FE renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Data.Bool renaming (_≟_ to _≟b_)
open import Data.List renaming (map to lmap)
open import Relation.Binary.PropositionalEquality as PE hiding ( Reveal_·_is_;[_];isEquivalence)
open import Relation.Unary hiding (_⊆_;_⇒_)

open import Data.Fin hiding (_+_)

import Relation.Binary.EqReasoning as EqR

open import HeterogeneousVec

pattern _↦_ ar s = (ar , s)

open Setoid
open import Setoids

{- Multisort Signature -}
record Signature : Set₁ where 
  field
    sorts  : Set
    ops    : (List sorts) × sorts → Set

  Arity : Set
  Arity = List sorts

  Type : Set
  Type = List sorts × sorts

open Signature

module Universe (Σ : Signature) where
  Universe : ∀  ℓ₁ ℓ₂ → Set _
  Universe ℓ₁ ℓ₂ = (s : sorts Σ) → Setoid ℓ₁ ℓ₂

  _⟶ₛ_ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} →
         (X : Universe ℓ₁ ℓ₂) → (Y : Universe ℓ₃ ℓ₄) → Set _
  X ⟶ₛ Y = (s : sorts Σ) → X s ⟶ Y s

open Universe
{- Algebra -}
record Algebra {ℓ₁ ℓ₂ : Level} (Σ : Signature) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  constructor _∥_

  field
    _⟦_⟧ₛ   : Universe Σ ℓ₁ ℓ₂
    _⟦_⟧ₒ    : ∀ {ar s} → ops Σ (ar , s) →
                _⟦_⟧ₛ ✳ ar ⟶ _⟦_⟧ₛ s

  _⟦_⟧ₛ* : (ar : Arity Σ) → Set _
  _⟦_⟧ₛ* ar = ∥ _⟦_⟧ₛ ✳ ar ∥

open Algebra

{- A class of algebras is a predicate over algebras -}
AlgClass : ∀ {ℓ₀ ℓ₁} Σ → Set (lsuc (ℓ₀ ⊔ ℓ₁))
AlgClass {ℓ₀} {ℓ₁} Σ = Algebra {ℓ₀} {ℓ₁} Σ → Set (ℓ₀ ⊔ ℓ₁)

{- Subalgebras -}
open SetoidPredicate

OpClosed : ∀ {ℓ₁ ℓ₂ ℓ₃ Σ} → (A : Algebra {ℓ₁} {ℓ₂} Σ) →
                  (P : (s : sorts Σ) → Pred (∥ A ⟦ s ⟧ₛ ∥) ℓ₃) → Set _
OpClosed {ℓ₃ = ℓ₃} {Σ = Σ} A P = ∀ {ar s} (f : ops Σ (ar , s)) →
             (P ⇨v ⟨→⟩ P s) (A ⟦ f ⟧ₒ ⟨$⟩_)

-- Subalgebra condition: A subsetoid closed by operations.
record SubAlg {ℓ₃ ℓ₁ ℓ₂} {Σ} (A : Algebra {ℓ₁} {ℓ₂} Σ) :
                                          Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where

  field
    pr   : (s : sorts Σ) → SetoidPredicate {ℓ₃ = ℓ₃} (A ⟦ s ⟧ₛ)
    opClosed : OpClosed {Σ = Σ} A (λ s x → predicate (pr s) x)

  pcong : ∀ {ar} {v₁ v₂ : HVec (λ s → Carrier $ SubSetoid (A ⟦ s ⟧ₛ)
                                                 (predicate (pr s))) ar} →
            _∼v_ {l₁ = ℓ₂} {R = λ { s (a₁ , _) (a₂ , _) →
                                    Setoid._≈_ (A ⟦ s ⟧ₛ) a₁ a₂ } } v₁ v₂ →
            _∼v_ {l₁ = ℓ₂} {R = λ s → Setoid._≈_ (A ⟦ s ⟧ₛ)}
                           (map (λ _ → proj₁) v₁ )
                           (map (λ _ → proj₁) v₂)
  pcong {[]} {⟨⟩} ∼⟨⟩ = ∼⟨⟩
  pcong {i ∷ is} (∼▹ x eq) = ∼▹ x (pcong eq)
  

-- A subsetoid closed by operations is an Algebra.
SubAlgebra : ∀ {Σ} {ℓ₁ ℓ₂ ℓ₃} {A : Algebra {ℓ₁} {ℓ₂} Σ} →
                   SubAlg {ℓ₃ = ℓ₃} A → Algebra Σ
SubAlgebra {Σ} {A = A} S = is ∥ if 
           where
             open SubAlg S 
             is : sorts Σ → _
             is s = SubSetoid (A ⟦ s ⟧ₛ) (predicate (pr s))
             if : ∀ {ar} {s} → (f : ops Σ (ar , s)) → is ✳ ar ⟶ is s
             if {ar} {s} f = record { _⟨$⟩_ = λ v → (A ⟦ f ⟧ₒ ⟨$⟩ map (λ _ → proj₁) v)
                                         , opClosed f (⇨₂ v)
                                  ; cong = λ { {v₁} {v₂} eq → Π.cong (A ⟦ f ⟧ₒ) (pcong eq) }
                                  }

{- Congruence -}
record Congruence {ℓ₃ ℓ₁ ℓ₂} {Σ : Signature}
                  (A : Algebra {ℓ₁} {ℓ₂} Σ) : Set (lsuc ℓ₃ ⊔ ℓ₂ ⊔ ℓ₁) where
  field
    rel : (s : sorts Σ) → Rel (Carrier (A ⟦ s ⟧ₛ)) ℓ₃
    welldef : (s : sorts Σ) → WellDefRel (A ⟦ s ⟧ₛ) (rel s)
    cequiv : (s : sorts Σ) → IsEquivalence (rel s)
    csubst : ∀ {ar s} (f : ops Σ (ar , s)) → rel * =[ A ⟦ f ⟧ₒ ⟨$⟩_ ]⇒ rel s


open Congruence

_⊆_ : ∀ {ℓ₃ ℓ₁ ℓ₂} {Σ : Signature} {A : Algebra {ℓ₁} {ℓ₂} Σ} →
        Congruence {ℓ₃} A → Congruence {ℓ₃} A → Set _
Φ ⊆ Ψ = ∀ s → (rel Φ s) ⇒ (rel Ψ s)


{- Quotient Algebra -}
_/_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {Σ} → (A : Algebra {ℓ₁} {ℓ₂} Σ) → (C : Congruence {ℓ₃} A) →
                            Algebra {ℓ₁} {ℓ₃} Σ
A / C = (λ s → record { Carrier = Carrier (A ⟦ s ⟧ₛ)
                              ; _≈_ = rel C s
                              ; isEquivalence = cequiv C s })
               ∥
               (λ {ar} {s} f → record { _⟨$⟩_ = λ v → A ⟦ f ⟧ₒ ⟨$⟩ v
                                      ; cong = csubst C f } )
