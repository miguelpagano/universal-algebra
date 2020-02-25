-- Universal Algebra Library
--
-- Propositional logic.
--
module Examples.PLogic (V : Set) (vp vq vr : V) where

open import Data.Bool
open import Data.Empty
open import Data.List hiding (and ; or) renaming ([_] to [|_|])
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.String renaming (_++_ to _++s_) hiding (replicate)
open import Data.Unit hiding (setoid)
import Function as F
open import Function.Equality renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Level renaming (zero to lzero ; suc to lsuc)
open import Relation.Binary hiding (_⇒_)
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PropositionalEquality as PE hiding ([_])
open import Relation.Binary.PropositionalEquality  hiding ( _≢_)

import Equational
open import HeterogeneousVec
open import Morphisms
open import Setoids
open import SigMorphism
open import TermAlgebra
open import UnivAlgebra

data Opsₚ : List ⊤ × ⊤ → Set where
  t∙     : Opsₚ ([] , tt)
  f∙     : Opsₚ ([] , tt)
  neg    : Opsₚ ([| tt |] , tt)
  equiv  : Opsₚ (tt ∷ [| tt |] , tt)
  nequiv : Opsₚ (tt ∷ [| tt |] , tt)
  and    : Opsₚ (tt ∷ [| tt |] , tt)
  or     : Opsₚ (tt ∷ [| tt |] , tt)
  impl   : Opsₚ (tt ∷ [| tt |] , tt)
  conseq : Opsₚ (tt ∷ [| tt |] , tt)

Σₚ : Signature
Σₚ = record { sorts = ⊤ ; ops = Opsₚ }

open Signature

-- variables
Vₚ : sorts Σₚ → Set
Vₚ _ = V

open OpenTerm Σₚ (λ _ → V)

Formₚ : Set
Formₚ = HU tt

-- Variables for formulas
p : Formₚ
p = term (inj₂ vp) ⟨⟩

q : Formₚ
q = term (inj₂ vq) ⟨⟩

r : Formₚ
r = term (inj₂ vr) ⟨⟩

-- Constants
true∼ : Formₚ
true∼ = term (inj₁ t∙) ⟨⟩

false∼ : Formₚ
false∼ = term (inj₁ f∙) ⟨⟩

-- sintactic sugar
¬ : Formₚ → Formₚ
¬ t₀ = term neg (t₀ ▹ ⟨⟩)

_≐_ : Formₚ → Formₚ → Formₚ
t₁ ≐ t₂ = term equiv (t₁ ▹ t₂ ▹ ⟨⟩)

_≢_ : Formₚ → Formₚ → Formₚ
t₁ ≢ t₂ = term nequiv (t₁ ▹ t₂ ▹ ⟨⟩)

infixl 5 _≐_
infixl 5 _≢_

_∧∙_ : Formₚ → Formₚ → Formₚ
t₁ ∧∙ t₂ = term and (t₁ ▹ t₂ ▹ ⟨⟩)

_∨∙_ : Formₚ → Formₚ → Formₚ
t₁ ∨∙ t₂ = term or (t₁ ▹ t₂ ▹ ⟨⟩)

infixl 6 _∨∙_
infixl 6 _∧∙_

_⇒_ : Formₚ → Formₚ → Formₚ
t₁ ⇒ t₂ = term impl (t₁ ▹ t₂ ▹ ⟨⟩)

_⇐_ : Formₚ → Formₚ → Formₚ
t₁ ⇐ t₂ = term conseq (t₁ ▹ t₂ ▹ ⟨⟩)

open Equational Σₚ
Ax₁ : Equation Vₚ _
Ax₁ = ⋀ p ≐ (q ≐ r) ≈ ((p ≐ q) ≐ r)

Ax₂ : Equation Vₚ _
Ax₂ = ⋀ (p ≐ q) ≈ (q ≐ p)

Ax₃ : Equation Vₚ _
Ax₃ = ⋀ p ≐ true∼ ≈ p

Ax₄ : Equation Vₚ _
Ax₄ = ⋀ p ∨∙ (q ∨∙ r) ≈ ((p ∨∙ q) ∨∙ r)

Ax₅ : Equation Vₚ _
Ax₅ = ⋀ (p ∨∙ q) ≈ (q ∨∙ p)

Ax₆ : Equation Vₚ _
Ax₆ = ⋀ p ∨∙ false∼ ≈ p

Ax₇ : Equation Vₚ _
Ax₇ = ⋀ p ∨∙ p ≈ p

Ax₈ : Equation Vₚ _
Ax₈ = ⋀ p ∨∙ (q ≐ r) ≈ (p ∨∙ q ≐ p ∨∙ r)

Ax₉ : Equation Vₚ _
Ax₉ = ⋀ ¬ p ≈ (p ≐ false∼)

Ax₁₀ : Equation Vₚ _
Ax₁₀ = ⋀ p ≢ q ≈ ((¬ p) ≐ q)

Ax₁₁ : Equation Vₚ _
Ax₁₁ = ⋀ p ∧∙ q ≈ (p ≐ (q ≐ p ∨∙ q))

Ax₁₂ : Equation Vₚ _
Ax₁₂ = ⋀ p ⇒ q ≈ (p ∨∙ q ≐ q)

Ax₁₃ : Equation Vₚ _
Ax₁₃ = ⋀ p ⇐ q ≈ (q ⇒ p)

-- More axioms.

Ax≡≈ : Equation Vₚ _
Ax≡≈ = ⋀ p ≈ₑ q if ( [| tt |] , ((p ≐ q) ≈ₑ true∼) ▹ ⟨⟩)

AxRefl≡ : Equation Vₚ _
AxRefl≡ = ⋀ p ≐ p ≈ true∼

Tₚ : Theory (λ _ → V) (replicate 15 tt)
Tₚ = Ax₁ ▹ Ax₂ ▹ Ax₃ ▹ Ax₄ ▹ Ax₅ ▹ Ax₆ ▹ Ax₇ ▹
     Ax₈ ▹ Ax₉ ▹ Ax₁₀ ▹ Ax₁₁ ▹ Ax₁₂ ▹ Ax₁₃ ▹ Ax≡≈ ▹ AxRefl≡ ▹ ⟨⟩

-- Patterns for the axioms.
pattern axₚ₁ = here
pattern axₚ₂ = there here
pattern axₚ₃ = there (there here)
pattern axₚ₄ = there (there (there here))
pattern axₚ₅ = there (there (there (there here)))
pattern axₚ₆ = there (there (there (there (there here))))
pattern axₚ₇ = there (there (there (there (there (there here)))))
pattern axₚ₈ = there (there (there (there (there (there (there here))))))
pattern axₚ₉ = there (there (there (there (there (there (there (there here)))))))
pattern axₚ₁₀ = there (there (there (there (there (there (there
                                                      (there (there here))))))))
pattern axₚ₁₁ = there (there (there (there (there (there (there (there (there
                                                            (there here)))))))))
pattern axₚ₁₂ = there (there (there (there (there (there (there (there (there
                                                    (there (there here))))))))))
pattern axₚ₁₃ = there (there (there (there (there (there (there (there (there
                                            (there (there (there here)))))))))))
pattern ax≡≈ = there (there (there (there (there (there (there (there (there
                                            (there (there (there (there here))))))))))))
pattern axrefl≡ = there (there (there (there (there (there (there (there (there
                                            (there (there (there (there (there here)))))))))))))

pattern noaxₚ = there (there (there (there (there (there (there (there (there
                                            (there (there (there (there (there (there ()))))))))))))))


-- Bool es álgebra de Tₚ
module BoolModel where

  Bsort : sorts Σₚ → Setoid _ _
  Bsort _ = PE.setoid Bool

  _=b_ : Bool → Bool → Bool
  false =b b = not b
  true =b b = b

  _≠b_ : Bool → Bool → Bool
  b ≠b b' = not (b =b b')

  _⇒b_ : Bool → Bool → Bool
  b ⇒b b' = (b ∨ b') =b b'

  Bops : ∀ {ar s} → ops Σₚ (ar , s) →
           Bsort ✳ ar ⟶ Bsort s
  Bops t∙ = record { _⟨$⟩_ = λ ⟨⟩ → true ; cong = λ { _ → PE.refl } }
  Bops f∙ = record { _⟨$⟩_ = λ ⟨⟩ → false ; cong = λ { _ → PE.refl } }
  Bops neg = record { _⟨$⟩_ = λ { (b ▹ ⟨⟩) → not b } ;
                      cong = λ { {b₀ ▹ ⟨⟩} {b₁ ▹ ⟨⟩} (∼▹ b₀≡b₁ _) → PE.cong not b₀≡b₁ } }
  Bops equiv = record { _⟨$⟩_ = λ { (b ▹ b' ▹ ⟨⟩) → b =b b' } ;
                        cong = λ { {b₀ ▹ b₀' ▹ ⟨⟩} {b₁ ▹ b₁' ▹ ⟨⟩} (∼▹ b₀≡b₁ (∼▹ b₀'≡b₁' ∼⟨⟩)) →
                                 cong₂ _=b_ b₀≡b₁ b₀'≡b₁' } }
  Bops nequiv = record { _⟨$⟩_ = λ { (b ▹ b' ▹ ⟨⟩) → b ≠b b' } ;
                       cong = λ { {b₀ ▹ b₀' ▹ ⟨⟩} {b₁ ▹ b₁' ▹ ⟨⟩} (∼▹ b₀≡b₁ (∼▹ b₀'≡b₁' ∼⟨⟩)) →
                                cong₂ _≠b_ b₀≡b₁ b₀'≡b₁' } }
  Bops and = record { _⟨$⟩_ = λ { (b ▹ b' ▹ ⟨⟩) → b ∧ b' } ;
                            cong = λ { {b₀ ▹ b₀' ▹ ⟨⟩} {b₁ ▹ b₁' ▹ ⟨⟩} (∼▹ b₀≡b₁ (∼▹ b₀'≡b₁' ∼⟨⟩)) →
                                 cong₂ _∧_ b₀≡b₁ b₀'≡b₁' } }
  Bops or = record { _⟨$⟩_ = λ { (b ▹ b' ▹ ⟨⟩) → b ∨ b' } ;
                           cong = λ { {b₀ ▹ b₀' ▹ ⟨⟩} {b₁ ▹ b₁' ▹ ⟨⟩} (∼▹ b₀≡b₁ (∼▹ b₀'≡b₁' ∼⟨⟩)) →
                                cong₂ _∨_ b₀≡b₁ b₀'≡b₁' } }
  Bops impl = record { _⟨$⟩_ = λ { (b ▹ b' ▹ ⟨⟩) → b ⇒b b' } ;
                      cong = λ { {b₀ ▹ b₀' ▹ ⟨⟩} {b₁ ▹ b₁' ▹ ⟨⟩} (∼▹ b₀≡b₁ (∼▹ b₀'≡b₁' ∼⟨⟩)) →
                                 cong₂ _⇒b_ b₀≡b₁ b₀'≡b₁' } }
  Bops conseq = record { _⟨$⟩_ = λ { (b ▹ b' ▹ ⟨⟩) → b' ⇒b b } ;
                       cong = λ { {b₀ ▹ b₀' ▹ ⟨⟩} {b₁ ▹ b₁' ▹ ⟨⟩} (∼▹ b₀≡b₁ (∼▹ b₀'≡b₁' ∼⟨⟩)) →
                                cong₂ (λ b b' → b' ⇒b b) b₀≡b₁ b₀'≡b₁' } }


  B : Algebra Σₚ
  B = record { _⟦_⟧ₛ = Bsort ; _⟦_⟧ₒ = Bops }

  open Equ
  open Equation

  Bsat₁ : B ⊨ Ax₁
  Bsat₁ θ ⇨v⟨⟩ with θ vp | θ vq | θ vr
  Bsat₁ θ ⇨v⟨⟩ | false | false | false = refl
  Bsat₁ θ ⇨v⟨⟩ | false | false | true = refl
  Bsat₁ θ ⇨v⟨⟩ | false | true | c = refl
  Bsat₁ θ ⇨v⟨⟩ | true | b | c = refl

  Bsat₂ : B ⊨ Ax₂
  Bsat₂ θ ⇨v⟨⟩ with θ vp | θ vq
  Bsat₂ θ ⇨v⟨⟩ | false | false = refl
  Bsat₂ θ ⇨v⟨⟩ | false | true = refl
  Bsat₂ θ ⇨v⟨⟩ | true | false = refl
  Bsat₂ θ ⇨v⟨⟩ | true | true = refl

  Bsat₃ : B ⊨ Ax₃
  Bsat₃ θ x with θ vp
  Bsat₃ θ x | false = refl
  Bsat₃ θ x | true = refl

  Bsat₄ : B ⊨ Ax₄
  Bsat₄ θ x with θ vp | θ vq | θ vr
  Bsat₄ θ x | false | false | false = refl
  Bsat₄ θ x | false | false | true = refl
  Bsat₄ θ x | false | true | false = refl
  Bsat₄ θ x | false | true | true = refl
  Bsat₄ θ x | true | false | false = refl
  Bsat₄ θ x | true | false | true = refl
  Bsat₄ θ x | true | true | false = refl
  Bsat₄ θ x | true | true | true = refl

  Bsat₅ : B ⊨ Ax₅
  Bsat₅ θ _ with θ vp | θ vq
  Bsat₅ θ x | false | false = refl
  Bsat₅ θ x | true | false = refl
  Bsat₅ θ x | false | true = refl
  Bsat₅ θ x | true | true = refl

  Bsat₆ : B ⊨ Ax₆
  Bsat₆ θ _ with θ vp
  Bsat₆ θ x | false = refl
  Bsat₆ θ x | true = refl

  Bsat₇ : B ⊨ Ax₇
  Bsat₇ θ _ with θ vp
  Bsat₇ θ x | false = refl
  Bsat₇ θ x | true = refl

  Bsat₈ : B ⊨ Ax₈
  Bsat₈ θ _ with θ vp | θ vq | θ vr
  Bsat₈ θ x | false | b | c = refl
  Bsat₈ θ x | true | b | c = refl

  Bsat₉ : B ⊨ Ax₉
  Bsat₉ θ _ with θ vp
  Bsat₉ θ x | false = refl
  Bsat₉ θ x | true = refl

  Bsat₁₀ : B ⊨ Ax₁₀
  Bsat₁₀ θ _ with θ vp | θ vq
  Bsat₁₀ θ x | false | false = refl
  Bsat₁₀ θ x | false | true = refl
  Bsat₁₀ θ x | true | b = refl

  Bsat₁₁ : B ⊨ Ax₁₁
  Bsat₁₁ θ _ with θ vp | θ vq
  Bsat₁₁ θ x | false | false = refl
  Bsat₁₁ θ x | false | true = refl
  Bsat₁₁ θ x | true | false = refl
  Bsat₁₁ θ x | true | true = refl

  Bsat₁₂ : B ⊨ Ax₁₂
  Bsat₁₂ θ _ = refl

  Bsat₁₃ : B ⊨ Ax₁₃
  Bsat₁₃ θ _ = refl

  boolabsurd : true ≡ false → ⊥
  boolabsurd ()

  Bsat≡≈ : B ⊨ Ax≡≈
  Bsat≡≈ θ satcond with θ vp | θ vq | inspect (θ) vp | inspect (θ) vq
  ... | true | true | c | d = refl
  ... | false | false | c | d = refl
  Bsat≡≈ θ (⇨v▹ x ⇨v⟨⟩) | true | false | [ eqp ] | [ eqq ] =
         ⊥-elim (boolabsurd (sym (subst₂ (λ b₁ b₂ → b₁ =b b₂ ≡ true) eqp eqq x)))
  Bsat≡≈ θ (⇨v▹ x ⇨v⟨⟩) | false | true | [ eqp ] | [ eqq ] =
         ⊥-elim (boolabsurd (sym (subst₂ (λ b₁ b₂ → b₁ =b b₂ ≡ true) eqp eqq x)))

  BsatRefl≡ : B ⊨ AxRefl≡
  BsatRefl≡ θ _ with θ vp
  BsatRefl≡ θ x | false = refl
  BsatRefl≡ θ x | true = refl

  Bsat : _⊨T_ B Tₚ
  Bsat = sall
    where sall : ∀ {s : ⊤} {e} → e ∈ Tₚ → B ⊨ e
          sall axₚ₁  = Bsat₁
          sall axₚ₂ = Bsat₂
          sall axₚ₃ = Bsat₃
          sall axₚ₄ = Bsat₄
          sall axₚ₅ = Bsat₅
          sall axₚ₆ = Bsat₆
          sall axₚ₇ = Bsat₇
          sall axₚ₈ = Bsat₈
          sall axₚ₉ = Bsat₉
          sall axₚ₁₀ = Bsat₁₀
          sall axₚ₁₁ = Bsat₁₁
          sall axₚ₁₂ = Bsat₁₂
          sall axₚ₁₃ = Bsat₁₃
          sall ax≡≈ = Bsat≡≈
          sall axrefl≡ = BsatRefl≡
          sall noaxₚ



printF : (pv : V → String) → Formₚ → String
printF pv (term {[]} (inj₁ t∙) ⟨⟩) = "true"
printF pv (term {[]} (inj₁ f∙) ⟨⟩) = "false"
printF pv (term {[]} (inj₂ y) ⟨⟩) = pv y
printF pv (term {_ ∷ []} neg (f ▹ ⟨⟩)) = "¬ (" ++s (printF pv f) ++s ")"
printF pv (term {_ ∷ _ ∷ []} equiv (f₁ ▹ f₂ ▹ ⟨⟩)) =
                               "(" ++s (printF pv f₁) ++s ") ≡ (" ++s (printF pv f₂) ++s ")"
printF pv (term {.tt ∷ .tt ∷ []} nequiv (f₁ ▹ f₂ ▹ ⟨⟩)) =
                               "(" ++s (printF pv f₁) ++s ") ≢ (" ++s (printF pv f₂) ++s ")"
printF pv (term {.tt ∷ .tt ∷ []} and (f₁ ▹ f₂ ▹ ⟨⟩)) =
                               "(" ++s (printF pv f₁) ++s ") ∧ (" ++s (printF pv f₂) ++s ")"
printF pv (term {.tt ∷ .tt ∷ []} or (f₁ ▹ f₂ ▹ ⟨⟩)) =
                               "(" ++s (printF pv f₁) ++s ") ∨ (" ++s (printF pv f₂) ++s ")"
printF pv (term {.tt ∷ .tt ∷ []} impl (f₁ ▹ f₂ ▹ ⟨⟩)) =
                            "(" ++s (printF pv f₁) ++s ") ⇒ (" ++s (printF pv f₂) ++s ")"
printF pv (term {.tt ∷ .tt ∷ []} conseq (f₁ ▹ f₂ ▹ ⟨⟩)) =
                            "(" ++s (printF pv f₁) ++s ") ⇐ (" ++s (printF pv f₂) ++s ")"
printF pv (term {_ ∷ _ ∷ _ ∷ _} () x₃)
