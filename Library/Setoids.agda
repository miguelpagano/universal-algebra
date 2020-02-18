module Setoids where

open import Data.Fin hiding (_+_)
open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)
open import Data.Sum
open import Level renaming (suc to lsuc ; zero to lzero)
open import Function as F
open import Function.Equality as FE renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Relation.Binary
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PropositionalEquality as PE
open import Relation.Unary

{- Carrier -}
∥_∥ : ∀ {l₁ l₂} → (Setoid l₁ l₂) → Set l₁
∥ S ∥ =  Carrier
  where open Setoid S

≡to≈ : ∀ {ℓ₁ ℓ₂} → (S : Setoid ℓ₁ ℓ₂) →
        {x y : ∥ S ∥ } → x PE.≡ y → Setoid._≈_ S x y
≡to≈ S PE.refl = Setoid.refl S

-- Extensional Equality
module ExtEq {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Setoid ℓ₁ ℓ₂} {B : Setoid ℓ₃ ℓ₄} where
  private
    _≈B_ : _
    _≈B_ = Setoid._≈_ B

    _≈A_ : _
    _≈A_ = Setoid._≈_ A

  open Setoid B
  _≈→_ : Rel (A ⟶ B) _
  f ≈→ g  = ∀ (a : ∥ A ∥) → (f ⟨$⟩ a) ≈B (g ⟨$⟩ a)

  ext-preserves-≈ : ∀ {a a' f g} → f ≈→ g → a ≈A a' → (f ⟨$⟩ a) ≈B (g ⟨$⟩ a')
  ext-preserves-≈ {a' = a'} {f} f≈g a≈a' = trans (Π.cong f a≈a') (f≈g a')

  Equiv≈→ : IsEquivalence (_≈→_)
  Equiv≈→ = record { refl = λ {f} a → refl {f ⟨$⟩ a}
                   ; sym = λ p a → sym (p a)
                   ; trans = λ p q a → trans (p a) (q a)
                   }

{- A predicate over a setoid should be even with respect to the equality -}
open Setoid
WellDef : ∀ {ℓ₁ ℓ₂ ℓ₃} → (S : Setoid ℓ₁ ℓ₂) → Pred (Carrier S) ℓ₃ → Set _
WellDef S P = ∀ {x y : Carrier S } → _≈_ S x y → P x → P y

{- The union of two well-defined relations is well-defined -}
∪-WellDef : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} → {S : Setoid ℓ₁ ℓ₂} →
          {P : Pred (Carrier S) ℓ₃} → {Q : Pred (Carrier S) ℓ₄} →
          WellDef S P → WellDef S Q → WellDef S (P ∪ Q)
∪-WellDef P-wd Q-wd a≈b (inj₁ p-a) = inj₁ (P-wd a≈b p-a)
∪-WellDef P-wd Q-wd a≈b (inj₂ q-a) = inj₂ (Q-wd a≈b q-a)

{- The intersection of two well-defined relations is well-defined -}
∩-WellDef : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} → {S : Setoid ℓ₁ ℓ₂} →
          {P : Pred (Carrier S) ℓ₃} → {Q : Pred (Carrier S) ℓ₄} →
          WellDef S P → WellDef S Q → WellDef S (P ∩ Q)
∩-WellDef P-wd Q-wd a≈b (pa , qa) = P-wd a≈b pa , Q-wd a≈b qa

{- A binary relation over a setoid should be even with respect to the equality -}
open import Data.Product
WellDefRel : ∀ {ℓ₁ ℓ₂ ℓ₃} → (S : Setoid ℓ₁ ℓ₂) → Rel (Carrier S) ℓ₃ → Set _
WellDefRel S R = WellDef (×-setoid S S) (λ {(a , b) → R a b})


{- A pre-congruene is a well-defined equivalence relation -}
PreCong : ∀ {ℓ₁ ℓ₂ ℓ₃} → (S : Setoid ℓ₁ ℓ₂) → Rel (Carrier S) ℓ₃ → Set _
PreCong S R = WellDefRel S R × IsEquivalence R

{-  The setoid equality is finer than a pre-congruence -}
PC-resp-~ : ∀ {ℓ₁ ℓ₂ ℓ₃} {S : Setoid ℓ₁ ℓ₂} (R : Rel (Carrier S) ℓ₃) →
  PreCong S R → {x y : Carrier S} → _≈_ S x y → R x y
PC-resp-~ {S = S} R (wd , isEq) {x} {y} eq = wd (refl S {x} , eq)
                                                (IsEquivalence.refl isEq {x})


{- A setoid predicate is a well-defined predicate over a setoid -}
record SetoidPredicate {ℓ₁ ℓ₂ ℓ₃} (S : Setoid ℓ₁ ℓ₂) :
                           Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃))  where
  field
    predicate   : Pred (Carrier S) ℓ₃
    predWellDef : WellDef S predicate

open SetoidPredicate

∪-SetoidPred : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {S : Setoid ℓ₁ ℓ₂} →
               SetoidPredicate {ℓ₃ = ℓ₃} S → SetoidPredicate {ℓ₃ = ℓ₄} S  →
               SetoidPredicate {ℓ₃ = ℓ₃ ⊔ ℓ₄} S
∪-SetoidPred {S = S} P Q = record {
                             predicate = predicate P ∪ predicate Q
                           ; predWellDef = ∪-WellDef {S = S} (predWellDef P)  (predWellDef Q)
                           }

∩-SetoidPred : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {S : Setoid ℓ₁ ℓ₂} →
               SetoidPredicate {ℓ₃ = ℓ₃} S → SetoidPredicate {ℓ₃ = ℓ₄} S  →
               SetoidPredicate {ℓ₃ = ℓ₃ ⊔ ℓ₄} S
∩-SetoidPred {S = S} P Q = record {
                             predicate = predicate P ∩ predicate Q
                           ; predWellDef = ∩-WellDef {S = S} (predWellDef P)  (predWellDef Q)
                           }

Subset : ∀ {ℓ₁ ℓ₂} → (A : Set ℓ₁) → (Pred A ℓ₂) → Set _
Subset A P = Σ[ a ∈ A ] (P a)

{- A setoid predicate defines a setoid -}
SubSetoid : ∀ {ℓ₁ ℓ₂ ℓ₃} (S : Setoid ℓ₁ ℓ₂) → (P : Pred ∥ S ∥ ℓ₃) →
                         Setoid _ _
SubSetoid S P = record { Carrier = Subset (Carrier S) P
                       ; _≈_ = λ { (e₁ , _) (e₂ , _) → (_≈_ S) e₁ e₂ }
                       ; isEquivalence = pequiv
                       }
  where pequiv : _
        pequiv = record { refl = refl S
                        ; sym = sym S
                        ; trans = trans S }


private
-- A more explicit version of well-defined relations.
  WellDefRel' : ∀ {ℓ₁ ℓ₂ ℓ₃} → (S : Setoid ℓ₁ ℓ₂) → Rel (Carrier S) ℓ₃ → Set _
  WellDefRel' S R = ∀ {a b c d} → _≈_ S a c → _≈_ S b d → R a b → R c d

  W↔W' : ∀ {ℓ₁ ℓ₂ ℓ₃} → (S : Setoid ℓ₁ ℓ₂) → (R : Rel (Carrier S) ℓ₃) → WellDefRel' S R → WellDefRel S R
  W↔W' S R wd {(a , b)} {(c , d)} (eq , eq') pa = wd eq eq' pa

  W'↔W : ∀ {ℓ₁ ℓ₂ ℓ₃} → (S : Setoid ℓ₁ ℓ₂) → (R : Rel (Carrier S) ℓ₃) → WellDefRel S R → WellDefRel' S R
  W'↔W S R wd {a} {b} {c} {d} eq  eq' pa = wd (eq , eq') pa


-- Indexed Setoids
module IndexedSetoid {ℓ₁ ℓ₂ ℓ₃ } {I : Set ℓ₁} (A : I → Setoid ℓ₂ ℓ₃ ) where

  private
    carrier : I → Set ℓ₂
    carrier i = Carrier (A i)
    ≈ᵢ : Rel ((i : I) → (carrier i)) (ℓ₁ ⊔ ℓ₃)
    ≈ᵢ f g = ∀ i → _≈_ (A i) (f i) (g i)
    isEquiv : IsEquivalence ≈ᵢ
    isEquiv = record
      { refl = λ i → refl (A i)
      ; sym = λ x i → sym (A i) (x i)
      ; trans = λ x x₁ i → trans (A i) (x i) (x₁ i)
      }

  Π-setoid : Setoid (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₃)
  Π-setoid = record {
    Carrier = (i : I) → carrier i
    ; _≈_ = ≈ᵢ
    ; isEquivalence = isEquiv
    }
