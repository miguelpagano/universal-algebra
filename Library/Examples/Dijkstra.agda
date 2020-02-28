
open import Relation.Binary hiding (_⇒_)
open import Level renaming (suc to lsuc ; zero to lzero)

module Examples.Dijkstra where

open import Data.Product renaming (map to pmap)
open import Function as F
open import Function.Equality as FE renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Data.List renaming (map to lmap) hiding (and ; or)
open import Relation.Binary.PropositionalEquality as PE hiding (_≢_)
open import Data.Fin hiding (_≟_)
open import Data.Vec
open import Data.Nat
open import Relation.Nullary hiding (¬_)
open import Data.Product

import Relation.Binary.EqReasoning as EqR



data Formula : Set where
  true  : Formula
  false : Formula
  var   : (p : ℕ) → Formula
  ¬     : (φ : Formula) → Formula
  _≡'_  : (φ₁ : Formula) → (φ₂ : Formula) → Formula
  _/≡_  : (φ₁ : Formula) → (φ₂ : Formula) → Formula
  _∧_   : (φ₁ : Formula) → (φ₂ : Formula) → Formula
  _∨_   : (φ₁ : Formula) → (φ₂ : Formula) → Formula
  _⇒_  : (φ₁ : Formula) → (φ₂ : Formula) → Formula
  _⇐_  : (φ₁ : Formula) → (φ₂ : Formula) → Formula


cong⁻¹≡ : ∀ {φ ψ φ' ψ'} → φ ≡' ψ ≡ φ' ≡' ψ' → φ ≡ φ' × ψ ≡ ψ'
cong⁻¹≡ refl = refl , refl


-- Esquema de axiomas

assoc≡ : (φ ψ τ : Formula) → Formula
assoc≡ φ ψ τ = (φ ≡' (ψ ≡' τ)) ≡' ((φ ≡' ψ) ≡' τ)

comm≡ : (φ ψ : Formula) → Formula
comm≡ φ ψ = (φ ≡' ψ) ≡' (ψ ≡' φ)

neu≡ : (φ : Formula) → Formula
neu≡ φ = (φ ≡' true) ≡' φ

assoc∨ : (φ ψ τ : Formula) → Formula
assoc∨ φ ψ τ = ((φ ∨ (ψ ∨ τ)) ≡' ((φ ∨ ψ) ∨ τ))

comm∨ : (φ ψ : Formula) → Formula
comm∨ φ ψ = (φ ∨ ψ) ≡' (ψ ∨ φ)

neu∨ : (φ : Formula) → Formula
neu∨ φ = (φ ∨ false) ≡' φ

idemp∨ : (φ : Formula) → Formula
idemp∨ φ = (φ ∨ φ) ≡' φ

dist∨ : (φ ψ τ : Formula) → Formula
dist∨ φ ψ τ = (φ ∨ (ψ ≡' τ)) ≡' ((φ ∨ ψ) ≡' (φ ∨ τ))

defFalse : (φ : Formula) → Formula
defFalse φ = (¬ φ ≡' (φ ≡' false))

def/≡ : (φ ψ : Formula) → Formula
def/≡ φ ψ = (φ /≡ ψ) ≡' ((¬ φ) ≡' ψ)

goldenR : (φ ψ : Formula) → Formula
goldenR φ ψ = (φ ∧ ψ) ≡' (φ ≡' (ψ ≡' (φ ∨ ψ)))

def⇒ : (φ ψ : Formula) → Formula
def⇒ φ ψ = (φ ⇒ ψ) ≡' ((φ ∨ ψ) ≡' ψ)

def⇐ : (φ ψ : Formula) → Formula
def⇐ φ ψ = (φ ⇐ ψ) ≡' (ψ ⇒ φ)

Axioms : (φ ψ τ : Formula) → Vec Formula 13
Axioms φ ψ τ = assoc≡ φ ψ τ ∷ comm≡ φ ψ ∷ neu≡ φ ∷ assoc∨ φ ψ τ ∷
               comm∨ φ ψ ∷ neu∨ φ ∷ idemp∨ φ ∷ dist∨ φ ψ τ ∷ defFalse φ ∷
               def/≡ φ ψ ∷ goldenR φ ψ ∷ def⇒ φ ψ ∷ def⇐ φ ψ ∷ []

import Data.Vec.Membership.Propositional
open Data.Vec.Membership.Propositional

open import Data.Vec.Relation.Unary.Any
-- patterns para los axiomas
pattern ax₁ = here refl
pattern ax₂ = there (here refl)
pattern ax₃ = there (there (here refl))
pattern ax₄ = there (there (there (here refl)))
pattern ax₅ = there (there (there (there (here refl))))
pattern ax₆ = there (there (there (there (there (here refl)))))
pattern ax₇ = there (there (there (there (there (there (here refl))))))
pattern ax₈ = there (there (there (there (there (there (there (here refl)))))))
pattern ax₉ = there (there (there (there (there (there (there (there (here refl))))))))
pattern ax₁₀ = there (there (there (there (there (there (there
                                                      (there (there (here refl)))))))))
pattern ax₁₁ = there (there (there (there (there (there (there (there (there
                                                            (there (here refl))))))))))
pattern ax₁₂ = there (there (there (there (there (there (there (there (there
                                                    (there (there (here refl)))))))))))
pattern ax₁₃ = there (there (there (there (there (there (there (there (there
                                            (there (there (there (here refl))))))))))))
pattern noax = there (there (there (there (there (there (there (there (there
                            (there (there (there (there ()))))))))))))



_[_:=_] : Formula → ℕ → Formula → Formula
true [ p := ψ ] = true
false [ p := ψ ] = false
var q [ p := ψ ] with p ≟ q
var q [ p := ψ ] | yes _ = ψ
var q [ p := ψ ] | no _ = var q
¬ φ [ p := ψ ] = ¬ (φ [ p := ψ ])
(φ₁ ≡' φ₂) [ p := ψ ] = (φ₁ [ p := ψ ]) ≡' (φ₂ [ p := ψ ])
(φ₁ /≡ φ₂) [ p := ψ ] = (φ₁ [ p := ψ ]) /≡ (φ₂ [ p := ψ ])
(φ₁ ∧ φ₂) [ p := ψ ] = (φ₁ [ p := ψ ]) ∧ (φ₂ [ p := ψ ])
(φ₁ ∨ φ₂) [ p := ψ ] = (φ₁ [ p := ψ ]) ∨ (φ₂ [ p := ψ ])
(φ₁ ⇒ φ₂) [ p := ψ ] = (φ₁ [ p := ψ ]) ⇒ (φ₂ [ p := ψ ])
(φ₁ ⇐ φ₂) [ p := ψ ] = (φ₁ [ p := ψ ]) ⇐ (φ₂ [ p := ψ ])


data ⊢_ : Formula → Set where
  ax    : ∀ {φ φ' ψ τ} → φ ∈ (Axioms φ' ψ τ) → ⊢ φ
  equan : ∀ {φ ψ} → ⊢ ψ → ⊢ (ψ ≡' φ) → ⊢ φ
  leib  : ∀ {φ ψ τ p} → ⊢ (ψ ≡' τ) → ⊢ ((φ [ p := ψ ]) ≡' (φ [ p := τ ]))


-- Example 1
module Example1 where

  1∙ : ⊢ (((true ≡' true) ≡' true) ≡' (true ≡' true))
  1∙ = ax {ψ = true} {τ = true} (there (there (here refl)))

  2∙ : ⊢ ((true ≡' true) ≡' true)
  2∙ = ax {ψ = true} {τ = true} ((there (there (here refl))))

  3∙ : ⊢ (true ≡' true)
  3∙ = equan 2∙ 1∙

  4∙ : ⊢ true
  4∙ = equan 3∙ 2∙



module ToEquational where
  open import Examples.PLogic ℕ 0 1 2 renaming (¬ to ¬ₚ ; _⇒_ to _⇒ₚ_ ; _⇐_ to _⇐ₚ_)
  open import UnivAlgebra
  import Equational
  open import HeterogeneousVec renaming (_∈_ to _∈ₕ_)
  open import Data.Sum
  open import TermAlgebra
  open OpenTerm Σₚ (λ _ → ℕ)

  ⟦_⟧ : Formula → Formₚ
  ⟦ true ⟧ = true∼
  ⟦ false ⟧ = false∼
  ⟦ var p ⟧ = term (inj₂ p) ⟨⟩
  ⟦ ¬ f ⟧ = ¬ₚ ⟦ f ⟧
  ⟦ f₁ ≡' f₂ ⟧ = ⟦ f₁ ⟧ ≐ ⟦ f₂ ⟧
  ⟦ f₁ /≡ f₂ ⟧ = ⟦ f₁ ⟧ ≢ ⟦ f₂ ⟧
  ⟦ f₁ ∧ f₂ ⟧ = ⟦ f₁ ⟧ ∧∙ ⟦ f₂ ⟧
  ⟦ f₁ ∨ f₂ ⟧ = ⟦ f₁ ⟧ ∨∙ ⟦ f₂ ⟧
  ⟦ f₁ ⇒ f₂ ⟧ = ⟦ f₁ ⟧ ⇒ₚ ⟦ f₂ ⟧
  ⟦ f₁ ⇐ f₂ ⟧ = ⟦ f₁ ⟧ ⇐ₚ ⟦ f₂ ⟧


  open Subst

  -- Traducción de axiomas
  {- Las metavariables φ' ψ' y τ que se utilizan para los meta-axiomas, son reemplazadas
     por las variables 0, 1 y 2 en el cálculo ecuacional. La substitución
     subsₐ φ' ψ' y τ formaliza eso -}

  subsₐ : (φ' ψ' τ : Formula) → Subst {Σₚ} {Vₚ} {Vₚ}
  subsₐ φ' ψ' τ  0 = ⟦ φ' ⟧
  subsₐ φ' ψ' τ  1 = ⟦ ψ' ⟧
  subsₐ φ' ψ' τ  2 = ⟦ τ ⟧
  subsₐ φ' ψ' τ  n = term (inj₂ n) ⟨⟩

  open Equational Σₚ

  ⟦_⟧ₐ : ∀ {φ' ψ' τ φ ψ} → (φ ≡' ψ) ∈ Axioms φ' ψ' τ → Tₚ ⊢ (⋀ Vₚ , ⟦ φ ⟧ ≈ ⟦ ψ ⟧)
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₁ = psubst axₚ₁ (subsₐ φ' ψ' τ) ⇨v⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₂ = psubst axₚ₂ (subsₐ φ' ψ' τ) ⇨v⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₃ = psubst axₚ₃ (subsₐ φ' ψ' τ) ⇨v⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₄ = psubst axₚ₄ (subsₐ φ' ψ' τ) ⇨v⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₅ = psubst axₚ₅ (subsₐ φ' ψ' τ) ⇨v⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₆ = psubst axₚ₆ (subsₐ φ' ψ' τ) ⇨v⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₇ = psubst axₚ₇ (subsₐ φ' ψ' τ) ⇨v⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₈ = psubst axₚ₈ (subsₐ φ' ψ' τ) ⇨v⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₉ = psubst axₚ₉ (subsₐ φ' ψ' τ) ⇨v⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₁₀ = psubst axₚ₁₀ (subsₐ φ' ψ' τ) ⇨v⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₁₁ = psubst axₚ₁₁ (subsₐ φ' ψ' τ) ⇨v⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₁₂ = psubst axₚ₁₂ (subsₐ φ' ψ' τ) ⇨v⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₁₃ = psubst axₚ₁₃ (subsₐ φ' ψ' τ) ⇨v⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} {φ} {ψ} noax

  
  -- Entonces ahora traducimos cualquier prueba del sistema formal, en una
  -- prueba ecuacional.

  pequan₁ : (φ ψ : Formula) →
            Tₚ ⊢ (⋀ Vₚ , ⟦ ψ ⟧ ≈ true∼) → Tₚ ⊢ (⋀ Vₚ , ⟦ ψ ⟧ ≈ ⟦ φ ⟧) →
            Tₚ ⊢ (⋀ Vₚ , ⟦ φ ⟧ ≈ true∼)
  pequan₁ φ ψ ⋀ψ≈t ⋀ψ≈φ = psym (ptrans (psym ⋀ψ≈t) ⋀ψ≈φ)
  pequan₂ : (φ ψ ψ₁ ψ₂ : Formula) → Tₚ ⊢ (⋀ Vₚ , ⟦ ψ₁ ⟧ ≈ ⟦ ψ₂ ⟧) → ψ ≡ ψ₁ ≡' ψ₂ →
            Tₚ ⊢ (⋀ Vₚ , ⟦ ψ ⟧ ≈ ⟦ φ ⟧) → Tₚ ⊢ (⋀ Vₚ , ⟦ φ ⟧ ≈ true∼)
  pequan₂ φ ψ ψ₁ ψ₂ ⋀ψ₁≈ψ₂ ψ=ψ₁≡ψ₂ ⋀ψ≈φ = ptrans (psym (ptrans
              (psym (preemp (⇨v▹ ⋀ψ₁≈ψ₂ (⇨v▹ prefl ⇨v⟨⟩))))
              (subst (λ ψ₀ → Tₚ ⊢ (⋀ Vₚ , ⟦ ψ₀ ⟧ ≈ ⟦ φ ⟧)) ψ=ψ₁≡ψ₂ ⋀ψ≈φ)))
                   reflψ₂
    where subs₀ : Subst
          subs₀ 0 = ⟦ ψ₂ ⟧
          subs₀ n = term (inj₂ n) ⟨⟩
          reflψ₂ : Tₚ ⊢ (⋀ Vₚ , ⟦ ψ₂ ⟧ ≐ ⟦ ψ₂ ⟧ ≈ true∼)
          reflψ₂ = psubst axrefl≡ subs₀ ⇨v⟨⟩

  open Signature

  pleibin : ∀ {ψ τ φ₁ φ₂ p} → (σ : ops Σₚ (_ ∷ _ ∷ [] , _)) →
              Tₚ ⊢ (⋀ Vₚ , ⟦ φ₁ [ p := ψ ] ⟧ ≈ ⟦ φ₁ [ p := τ ] ⟧) →
              Tₚ ⊢ (⋀ Vₚ , ⟦ φ₂ [ p := ψ ] ⟧ ≈ ⟦ φ₂ [ p := τ ] ⟧) →
              Tₚ ⊢ (⋀ Vₚ , term σ (⟦ φ₁ [ p := ψ ] ⟧ ▹ ⟦ φ₂ [ p := ψ ] ⟧ ▹ ⟨⟩) ≈
                      term σ (⟦ φ₁ [ p := τ ] ⟧ ▹ ⟦ φ₂ [ p := τ ] ⟧ ▹ ⟨⟩))
  pleibin σ p₁ p₂ = preemp (⇨v▹ p₁ (⇨v▹ p₂ ⇨v⟨⟩))

  pleib : ∀ {ψ τ φ p} → Tₚ ⊢ (⋀ Vₚ , ⟦ ψ ⟧ ≈ ⟦ τ ⟧) → Tₚ ⊢ (⋀ Vₚ , ⟦ φ [ p := ψ ] ⟧ ≈ ⟦ φ [ p := τ ] ⟧)
  pleib {φ = true} eqpru = prefl
  pleib {φ = false} eqpru = prefl
  pleib {ψ} {τ} {var q} {p} eqpru with p ≟ q
  ... | yes p₁ = eqpru
  ... | no ¬p = prefl
  pleib {ψ} {τ} {¬ φ} {p} eqpru = preemp (⇨v▹ (pleib {φ = φ} eqpru) ⇨v⟨⟩)
  pleib {ψ} {τ} {φ₁ ≡' φ₂} {p} eqpru = pleibin {φ₁ = φ₁} {φ₂}
                                               equiv (pleib {φ = φ₁} eqpru)
                                                     (pleib {φ = φ₂} eqpru)
  pleib {ψ} {τ} {φ₁ /≡ φ₂} {p} eqpru = pleibin {φ₁ = φ₁} {φ₂}
                                               nequiv (pleib {φ = φ₁} eqpru)
                                                     (pleib {φ = φ₂} eqpru)
  pleib {ψ} {τ} {φ₁ ∧ φ₂} {p} eqpru = pleibin {φ₁ = φ₁} {φ₂}
                                               and (pleib {φ = φ₁} eqpru)
                                                     (pleib {φ = φ₂} eqpru)
  pleib {ψ} {τ} {φ₁ ∨ φ₂} {p} eqpru = pleibin {φ₁ = φ₁} {φ₂}
                                               or (pleib {φ = φ₁} eqpru)
                                                     (pleib {φ = φ₂} eqpru)
  pleib {ψ} {τ} {φ₁ ⇒ φ₂} {p} eqpru = pleibin {φ₁ = φ₁} {φ₂}
                                               impl (pleib {φ = φ₁} eqpru)
                                                     (pleib {φ = φ₂} eqpru)
  pleib {ψ} {τ} {φ₁ ⇐ φ₂} {p} eqpru = pleibin {φ₁ = φ₁} {φ₂}
                                               conseq (pleib {φ = φ₁} eqpru)
                                                     (pleib {φ = φ₂} eqpru)

  substaux : ∀ {φ ψ φ' ψ'} → Tₚ ⊢ (⋀ Vₚ , ⟦ ψ' ⟧ ≈ ⟦ φ' ⟧) → (ψ ≡' φ) ≡ (ψ' ≡' φ') →
               Tₚ ⊢ (⋀ Vₚ , ⟦ ψ ⟧ ≈ ⟦ φ ⟧)
  substaux ⋀ψ'≈φ' ψ≡φ=ψ'≡φ' =
                  (subst₂ (λ φ' ψ' → Tₚ ⊢ (⋀ Vₚ , ⟦ φ' ⟧ ≈ ⟦ ψ' ⟧))
                         (proj₁ (cong⁻¹≡ (sym ψ≡φ=ψ'≡φ')))
                         (proj₂ (cong⁻¹≡ (sym ψ≡φ=ψ'≡φ'))) ⋀ψ'≈φ')

  p≡to≈ : ∀ {φ ψ} → Tₚ ⊢ (⋀ Vₚ , ⟦ φ ≡' ψ ⟧ ≈ true∼) → Tₚ ⊢ (⋀ Vₚ , ⟦ φ ⟧ ≈ ⟦ ψ ⟧)
  p≡to≈ {φ} {ψ} pru = psubst ax≡≈ subs₀ (⇨v▹ pru ⇨v⟨⟩)
    where subs₀ : Subst
          subs₀ 0 = ⟦ φ ⟧
          subs₀ 1 = ⟦ ψ ⟧
          subs₀ n = term (inj₂ n) ⟨⟩


  ⊢↝Eq : ∀ {φ} → (pru : ⊢ φ) → (Tₚ ⊢ (⋀ Vₚ , ⟦ φ ⟧ ≈ true∼)) ⊎
                                   (Σ[ φ' ∈ Formula ] (Σ[ ψ ∈ Formula ]
                                   ((Tₚ ⊢ (⋀ Vₚ , ⟦ φ' ⟧ ≈ ⟦ ψ ⟧)) × (φ ≡ φ' ≡' ψ))))
  ⊢↝Eq {φ ≡' ψ} (ax ∈A) = inj₂ (φ , ψ , (⟦ ∈A ⟧ₐ , refl))
  ⊢↝Eq {true} (ax noax)
  ⊢↝Eq {false} (ax noax)
  ⊢↝Eq {var p} (ax noax)
  ⊢↝Eq {¬ φ} (ax noax)
  ⊢↝Eq {φ /≡ φ₁} (ax noax)
  ⊢↝Eq {φ ∧ φ₁} (ax noax)
  ⊢↝Eq {φ ∨ φ₁} (ax noax)
  ⊢↝Eq {φ ⇒ φ₁} (ax noax)
  ⊢↝Eq {φ ⇐ φ₁} (ax noax)
  ⊢↝Eq {φ} (equan {.φ} {ψ} ⊢ψ ⊢ψ≡φ) with ⊢↝Eq ⊢ψ | ⊢↝Eq ⊢ψ≡φ
  ... | inj₁ ⋀ψ≈t | inj₂ (ψ' , φ' , ⋀ψ'≈φ' , ψ≡φ=ψ'≡φ') =
             inj₁ (pequan₁ φ ψ ⋀ψ≈t
                  (substaux ⋀ψ'≈φ' ψ≡φ=ψ'≡φ'))
  ... | inj₂ (ψ₁ , ψ₂ , ⋀ψ₁≈ψ₂ , ψ=ψ₁≡ψ₂) | inj₂ (ψ' , φ' , ⋀ψ'≈φ' , ψ≡φ=ψ'≡φ') =
            inj₁ (pequan₂ φ ψ ψ₁ ψ₂ ⋀ψ₁≈ψ₂ ψ=ψ₁≡ψ₂ (substaux ⋀ψ'≈φ' ψ≡φ=ψ'≡φ'))
  ... | inj₁ ⋀ψ≈t | inj₁ ⊢⋀ψ≡φ≈t =
            inj₁ (pequan₁ φ ψ ⋀ψ≈t (p≡to≈ {ψ} {φ} ⊢⋀ψ≡φ≈t))
  ... | inj₂ (ψ₁ , ψ₂ , ⋀ψ₁≈ψ₂ , ψ=ψ₁≡ψ₂) | inj₁ ⋀ψ≡φ≈t =
            inj₁ (pequan₂ φ ψ ψ₁ ψ₂ ⋀ψ₁≈ψ₂ ψ=ψ₁≡ψ₂ (p≡to≈ {ψ} {φ} ⋀ψ≡φ≈t))
  ⊢↝Eq (leib {φ} {ψ} {τ} {p} pru) with ⊢↝Eq pru
  ... | inj₁ ⋀ψ≡τ≈t =
                 inj₂ ((φ [ p := ψ ]) ,
                      ((φ [ p := τ ]) ,
                      (pleib {φ = φ} (p≡to≈ {ψ} {τ} ⋀ψ≡τ≈t) ,
                      refl)))
  ... | inj₂ (ψ₁ , τ₁ , ⋀ψ₁≈τ₁ , ψ≡τ=ψ₁≡τ₁) =
                 inj₂ ( (φ [ p := ψ ])
                      , ((φ [ p := τ ])
                      , ((pleib {φ = φ} (substaux ⋀ψ₁≈τ₁ ψ≡τ=ψ₁≡τ₁))
                      , refl)))




{- En PLogic hemos dado una teoría para la lógica proposicional, con 15 axiomas y
   probamos que Bool es un modelo, esto nos garantiza que las pruebas ecuacionales
   que podemos hacer son correctas.
   En la primera parte de este archivo definimos un sistema formal para la lógica
   proposicional, según el paper de Rocha. En ese paper dice que ese sistema es correcto
   y completo.
   En el módulo ToEquational definimos una traducción de toda prueba en el sistema formal
   en una prueba ecuacional para la teoría definida en PLogic. Puesto que el sistema de
   Rocha captura toda la lógica proposicional y que las pruebas ecuacionales son correctas,
   tenemos un cálculo ecuacional para la lógica proposicional correcto y completo.
-}


module Examples where
  open ToEquational
  open import Examples.PLogic ℕ 0 1 2 renaming (¬ to ¬ₚ ; _⇒_ to _⇒ₚ_ ; _⇐_ to _⇐ₚ_)
  open Example1
  open import Data.Nat.Show renaming (show to shown)
  open import Data.String
  open import UnivAlgebra
  import Equational
  open import HeterogeneousVec renaming (_∈_ to _∈ₕ_)
  open import Data.Sum

  open Equational Σₚ

  ex₁ : (Tₚ ⊢ (⋀ Vₚ , ⟦ true ⟧ ≈ true∼)) ⊎
        (Σ[ φ' ∈ Formula ] (Σ[ ψ ∈ Formula ]
        ((Tₚ ⊢ (⋀ Vₚ , ⟦ φ' ⟧ ≈ ⟦ ψ ⟧)) × (true ≡ φ' ≡' ψ))))
  ex₁ = ⊢↝Eq 4∙

  toproof : ∀ {φ} → (Tₚ ⊢ (⋀ Vₚ , ⟦ φ ⟧ ≈ true∼)) ⊎
                   (Σ[ φ' ∈ Formula ] (Σ[ ψ ∈ Formula ]
                   ((Tₚ ⊢ (⋀ Vₚ , ⟦ φ' ⟧ ≈ ⟦ ψ ⟧)) × (φ ≡ φ' ≡' ψ)))) →
                   (Σ[ φ' ∈ Formula ] (Σ[ ψ ∈ Formula ]
                   (Tₚ ⊢ (⋀ Vₚ , ⟦ φ' ⟧ ≈ ⟦ ψ ⟧))))
  toproof {φ} (inj₁ x) = φ , true , x
  toproof (inj₂ (φ' , ψ , pr , _)) = φ' , (ψ , pr)

{- TODO: this is broken!
  showex₁ : String
  showex₁ = printF shown prf
    where prf : _
          prf = proj₂ (proj₂ (toproof ex₁))

-}

open Examples
