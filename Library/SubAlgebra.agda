-- Universal Algebra Library
--
-- Algebras generated by a set and free-algebras.
-- DISCLAIMER: This is a file in progress.
--
open import UnivAlgebra
open import Level renaming (zero to lzero ; suc to lsuc)
module SubAlgebra (Σ : Signature) {ℓ₁ ℓ₂ : Level} (A : Algebra {ℓ₁} {ℓ₂} Σ) where

open import Data.List
open import Data.Product renaming (map to ×f) hiding (Σ)
open import Data.Sum
open import Function as F hiding (Injective; Bijective; Surjective; Inverse;
                          module Injection;Injection; module Bijection; Bijection;
                          module Inverse;_⟶_)
open import Function.Equality as FE renaming (_∘_ to _∘ₛ_) hiding (setoid;_⇨_)
open import Function.Bijection hiding (_∘_)
open import Function.Surjection hiding (_∘_)
open import Function.Injection renaming (_∘_ to _∘ᵢ_)
open import Relation.Binary
open import Relation.Unary renaming (_⊆_ to _⊆r_) hiding (_⇒_)
import Relation.Binary.Reasoning.Setoid as EqR
import Relation.Binary.PropositionalEquality as PE

-- import Equational
open import Morphisms {Σ}
open import Setoids
open import HeterogeneousVec renaming (map to mapV)
import TermAlgebra as T

-- Equivalent predicates induces an isomorphism of algebras.
open SetoidPredicate
open SubAlg
Predicate : (ℓ₃ : Level) → Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃))
Predicate ℓ₃ = (s : sorts Σ) → SetoidPredicate {ℓ₃ = ℓ₃} (A ⟦ s ⟧ₛ)

_⊆ₚ_ : ∀ {ℓ₃ ℓ₄} → Predicate ℓ₃ → Predicate ℓ₄ → Set (ℓ₁ ⊔ ℓ₃ ⊔ ℓ₄)
P ⊆ₚ Q = (s : sorts Σ) → predicate (P s) ⊆r predicate (Q s)

_⊆ₚ*_ : ∀ {ℓ₃ ℓ₄} → Predicate ℓ₃ → Predicate ℓ₄ → Set (ℓ₁ ⊔ ℓ₃ ⊔ ℓ₄)
P ⊆ₚ* Q = ∀ ar → ((λ {s} → (predicate ∘ P) s) ⇨v) ⊆r
                  ((predicate ∘ Q) $- ⇨v)  {is = ar}


≅-SubAlg : ∀ {ℓ₃ ℓ₄} → (B : SubAlg {ℓ₃ = ℓ₃} A) → (C : SubAlg {ℓ₃ = ℓ₄} A) → Set _
≅-SubAlg B C = pr B ⊆ₚ pr C × pr C ⊆ₚ pr B

≅-SubAlg-iso : ∀ {ℓ₃ ℓ₄} → {B : SubAlg {ℓ₃ = ℓ₃} A} → {C : SubAlg {ℓ₃ = ℓ₄} A} →
               ≅-SubAlg B C → Isomorphism (SubAlgebra B) (SubAlgebra C)
≅-SubAlg-iso {ℓ₃} {ℓ₄} {B} {C} (B≤C , C≤B) = record
  { hom = H
  ; bij = λ s → record
                  { injective = F.id
                  ; surjective = isSurj s
                  }
  }
  where
  open Hom
  ′H′ : ∀ s → (SubAlgebra B) ⟦ s ⟧ₛ ⟶ (SubAlgebra C) ⟦ s ⟧ₛ
  ′H′ s = record
    { _⟨$⟩_ = ×f F.id (B≤C s)
    ; cong = F.id
    }
  Hcond : homCond (SubAlgebra B) (SubAlgebra C) ′H′
  Hcond {s = s} f as
    rewrite map-compose (λ i → ×f F.id (B≤C i)) (λ _ → proj₁) as =
    Setoid.refl (A ⟦ s ⟧ₛ)
  H : Homo (SubAlgebra B) (SubAlgebra C)
  H = record { ′_′ = ′H′ ; cond = Hcond }

  H⁻¹ : ∀ s → (SubAlgebra C) ⟦ s ⟧ₛ ⟶ (SubAlgebra B) ⟦ s ⟧ₛ
  H⁻¹ s = record
    { _⟨$⟩_ = ×f F.id (C≤B s)
    ; cong = F.id
    }
  isSurj : ∀ s → Surjective (′ H ′ s)
  isSurj s = record
    { from = H⁻¹ s
    ; right-inverse-of = λ _ → Setoid.refl (A ⟦ s ⟧ₛ)
    }


-- The intersection of a family of subalgebras is a subalgebra.
⋂-SubAlg : ∀ {ℓ₃ ℓ₄} → (P : Pred (SubAlg {ℓ₃ = ℓ₃} A) ℓ₄) →
              SubAlg {ℓ₃ = lsuc ℓ₁ ⊔ lsuc ℓ₂ ⊔ lsuc ℓ₃ ⊔ ℓ₄} A
⋂-SubAlg {ℓ₃} {ℓ₄} P = record
  { pr = pred
  ; opClosed = λ f vs Q pq → opClosed Q f (map⇨v (λ v → v Q pq) vs)
  }
  where
  pred : Predicate _
  pred s = record
    { predicate = λ x → ∀ Q → P Q → predicate (pr Q s) x
    ; predWellDef = λ eq pres Q → predWellDef (pr Q s) eq ∘ pres Q
    }

-- Alternative inductive definition.
data E {ℓ₃} (X : Predicate ℓ₃) s : Setoid.Carrier (A ⟦ s ⟧ₛ) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  inX : ∀ {a} → predicate (X s) a → E X s a
  img : ∀ {a ar} {f : ops Σ (ar , s)} (ts : HVec (λ x → ∃ (E X x)) ar) →
        Setoid._≈_ (A ⟦ s ⟧ₛ) ((A ⟦ f ⟧ₒ ⟨$⟩ mapV (λ _ → proj₁) ts)) a →
              E X s a

E-WellDefined : ∀ {ℓ₃}→ (X : Predicate ℓ₃) → ∀ s → WellDef (A ⟦ s ⟧ₛ) (E X s)
E-WellDefined X s a≈b (inX x) = inX (predWellDef (X s) a≈b x)
E-WellDefined X s a≈b (img ts a≈f-ts) = img ts (trans a≈f-ts a≈b)
  where open Setoid (A ⟦ s ⟧ₛ)

E-Pred : ∀ {ℓ₃} → (X : Predicate ℓ₃) → Predicate _
E-Pred X s = record { predicate = E X s
                    ; predWellDef = E-WellDefined X s
                    }

X⊆E : ∀ {ℓ₃} (X : Predicate ℓ₃) → X ⊆ₚ E-Pred X
X⊆E X s a∈X = inX a∈X

E-opClosed : ∀ {ℓ₃} → (X : Predicate ℓ₃) → OpClosed A ((predicate ∘ E-Pred X) $-)
E-opClosed X {ar} {s} f {ts} tsp = img {f = f} (⇨vtoΣ tsp) prop
  where open Setoid (A ⟦ s ⟧ₛ)
        prop : (A ⟦ f ⟧ₒ) ⟨$⟩ mapV (λ _ → proj₁) (⇨vtoΣ tsp) ≈ (A ⟦ f ⟧ₒ) ⟨$⟩ ts
        prop rewrite proj₁-inv-⇨vtoΣ tsp = refl


E-SubAlg : ∀ {ℓ₃} → (X : Predicate ℓ₃) → SubAlg {ℓ₃ = ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃} A
E-SubAlg X = record { pr = E-Pred X ; opClosed = E-opClosed X }

-- Algebra generated by a SetoidPredicate (not necessarily OpClosed).
⟨_⟩ : ∀ {ℓ₃} → (X : Predicate ℓ₃) → Algebra Σ
⟨_⟩ {ℓ₃ = ℓ₃} X  = SubAlgebra (E-SubAlg X)

-- Equivalence between ⋂-SubAlg and E-SubAlg:
--   E X ≈ ⋂ {B | B ≤ A ∧ X ⊆ B}
E⊆⋂-Sub : ∀ {ℓ₃} → (X : Predicate ℓ₃) →
        pr (⋂-SubAlg {ℓ₃ = ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ } (λ Q → X ⊆ₚ pr Q)) ⊆ₚ E-Pred X
E⊆⋂-Sub X s a = a (E-SubAlg X) (X⊆E X)

⋂-Sub⊆E : ∀ {ℓ₃} → (X : Predicate ℓ₃) →
        E-Pred X ⊆ₚ
        pr (⋂-SubAlg {ℓ₃ = ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ } (λ Q → X ⊆ₚ pr Q))
⋂-Sub⊆E* : ∀ {ℓ₃} → (X : Predicate ℓ₃) → ∀ Q → X ⊆ₚ pr Q →
         ∀ {ar} (ts : HVec (λ x → ∃ (E X x)) ar) →
        ((predicate ∘ pr Q) $-) ⇨v mapV (λ _ → proj₁) ts

⋂-Sub⊆E X s (inX x) Q X⊆Q = X⊆Q s x
⋂-Sub⊆E X s (img {a} {ar} {f} tsE x) Q X⊆Q = predWellDef (pr Q s) x f-tsQ
  where f-tsQ : predicate (pr Q s) ((A ⟦ f ⟧ₒ) ⟨$⟩ mapV (λ _ → proj₁) tsE)
        f-tsQ = opClosed Q f (⋂-Sub⊆E* X Q X⊆Q tsE )

⋂-Sub⊆E* X Q X⊆Q ⟨⟩ = ⇨v⟨⟩
⋂-Sub⊆E* X Q X⊆Q {s ∷ _} (v ▹ ts) = ⇨v▹ (⋂-Sub⊆E X s (proj₂ v) Q X⊆Q)
                                            (⋂-Sub⊆E* X Q X⊆Q ts)

