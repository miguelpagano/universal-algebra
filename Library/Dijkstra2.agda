open import Relation.Binary hiding (_⇒_)
open import Level renaming (suc to lsuc ; zero to lzero)

module Dijkstra2 where

open import Data.Product renaming (map to pmap)
open import Function as F
open import Function.Equality as FE renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Data.List renaming (map to lmap)
open import Relation.Binary.PropositionalEquality as PE hiding (_≢_)
open import Data.Fin
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
cong⁻¹≡ eq = {!!}


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

-- patterns para los axiomas
pattern ax₁ = here
pattern ax₂ = there here
pattern ax₃ = there (there here)
pattern ax₄ = there (there (there here))
pattern ax₅ = there (there (there (there here)))
pattern ax₆ = there (there (there (there (there here))))
pattern ax₇ = there (there (there (there (there (there here)))))
pattern ax₈ = there (there (there (there (there (there (there here))))))
pattern ax₉ = there (there (there (there (there (there (there (there here)))))))
pattern ax₁₀ = there (there (there (there (there (there (there
                                                      (there (there here))))))))
pattern ax₁₁ = there (there (there (there (there (there (there (there (there
                                                            (there here)))))))))
pattern ax₁₂ = there (there (there (there (there (there (there (there (there
                                                    (there (there here))))))))))
pattern ax₁₃ = there (there (there (there (there (there (there (there (there
                                            (there (there (there here)))))))))))
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
  ax    : ∀ {φ φ' ψ τ} → φ ∈ Axioms φ' ψ τ → ⊢ φ
  equan : ∀ {φ ψ} → ⊢ ψ → ⊢ (ψ ≡' φ) → ⊢ φ
  leib  : ∀ {φ ψ τ p} → ⊢ (ψ ≡' τ) → ⊢ ((φ [ p := ψ ]) ≡' (φ [ p := τ ]))


-- Example 1
module Example1 where

  1∙ : ⊢ (((true ≡' true) ≡' true) ≡' (true ≡' true))
  1∙ = ax {ψ = true} {τ = true} ax₃

  2∙ : ⊢ ((true ≡' true) ≡' true)
  2∙ = ax {ψ = true} {τ = true} ax₃

  3∙ : ⊢ (true ≡' true)
  3∙ = equan 2∙ 1∙

  4∙ : ⊢ true
  4∙ = equan 3∙ 2∙



module ToEquational where
  open import PLogic ℕ 0 1 2 renaming (¬ to ¬ₚ ; _⇒_ to _⇒ₚ_ ; _⇐_ to _⇐ₚ_)
  open import UnivAlgebra
  open import Equational
  open import HeterogenuousVec renaming (_∈_ to _∈ₕ_)
  open import Data.Sum

  open TermAlgebra (Σₚ 〔 (λ _ → ℕ) 〕)

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


  open Subst {Σₚ} {λ _ → ℕ}

  -- Traducción de axiomas
  {- Las metavariables φ' ψ' y τ que se utilizan para los meta-axiomas, son reemplazadas
     por las variables 0, 1 y 2 en el cálculo ecuacional. La substitución
     subsₐ φ' ψ' y τ formaliza eso -}

  subsₐ : (φ' ψ' τ : Formula) → Subst
  subsₐ φ' ψ' τ _ 0 = ⟦ φ' ⟧
  subsₐ φ' ψ' τ _ 1 = ⟦ ψ' ⟧
  subsₐ φ' ψ' τ _ 2 = ⟦ τ ⟧
  subsₐ φ' ψ' τ _ n = term (inj₂ n) ⟨⟩ 


  ⟦_⟧ₐ : ∀ {φ' ψ' τ φ ψ} → (φ ≡' ψ) ∈ Axioms φ' ψ' τ → Tₚ ⊢ (⋀ ⟦ φ ⟧ ≈ ⟦ ψ ⟧)
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₁ = psubst axₚ₁ (subsₐ φ' ψ' τ) ∼⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₂ = psubst axₚ₂ (subsₐ φ' ψ' τ) ∼⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₃ = psubst axₚ₃ (subsₐ φ' ψ' τ) ∼⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₄ = psubst axₚ₄ (subsₐ φ' ψ' τ) ∼⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₅ = psubst axₚ₅ (subsₐ φ' ψ' τ) ∼⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₆ = psubst axₚ₆ (subsₐ φ' ψ' τ) ∼⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₇ = psubst axₚ₇ (subsₐ φ' ψ' τ) ∼⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₈ = psubst axₚ₈ (subsₐ φ' ψ' τ) ∼⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₉ = psubst axₚ₉ (subsₐ φ' ψ' τ) ∼⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₁₀ = psubst axₚ₁₀ (subsₐ φ' ψ' τ) ∼⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₁₁ = psubst axₚ₁₁ (subsₐ φ' ψ' τ) ∼⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₁₂ = psubst axₚ₁₂ (subsₐ φ' ψ' τ) ∼⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} ax₁₃ = psubst axₚ₁₃ (subsₐ φ' ψ' τ) ∼⟨⟩
  ⟦_⟧ₐ {φ'} {ψ'} {τ} {φ} {ψ} noax

  

  -- Para traducir pruebas, lo primero que vamos a hacer es
  -- pasar de una prueba de una fórmula a una que tenga siempre un equivalente.
  -- Si tenemos que la conclusión es φ ≡ ψ, listo. Sino, la cambiamos por φ ≡ true.

  ⊢↝≡ : ∀ {φ} → ⊢ φ → Σ[ φ' ∈ Formula ] (Σ[ ψ ∈ Formula ] (⊢ (φ' ≡' ψ)))
  ⊢↝≡ {φ' ≡' ψ} p = φ' , (ψ , p)
  ⊢↝≡ {φ} ⊢φ = φ , (true , pru)
    where pru : ⊢ (φ ≡' true)
          pru = equan ⊢φ (equan (ax {ψ = true} {τ = true} ax₃)
                                (ax {τ = true} ax₂)) 
                                

  _↝≡true : ∀ {φ} → ⊢ φ → ⊢ (φ ≡' true)
  _↝≡true {φ} ⊢φ = equan ⊢φ (equan (ax {ψ = true} {τ = true} ax₃)
                                     (ax {τ = true} ax₂)) 


  -- quizás esto debería ser un axioma:
  refl≡ : Tₚ ⊢ (⋀ (p ≐ p) ≈ true∼)
  refl≡ = {!!}

  -- Entonces ahora traducimos cualquier prueba del sistema formal, en una
  -- prueba ecuacional.

{-
  ⊢↝Eq₁ : ∀ {φ ψ} → (pru : ⊢ (φ ≡' ψ)) → Tₚ ⊢ (⋀ ⟦ φ ⟧ ≈ ⟦ ψ ⟧)
  ⊢↝Eq₁ (ax x) = ⟦ x ⟧ₐ
  ⊢↝Eq₁ {φ} {ψ} (equan ⊢φ' ⊢φ'≡φ≡ψ) = {!!}
  ⊢↝Eq₁ (leib ⊢φ≡ψ) = {!!}


  ⊢↝Eq : ∀ {φ} → (pru : ⊢ φ) → Tₚ ⊢ (⋀ ⟦ proj₁ (⊢↝≡ pru) ⟧ ≈
                                          ⟦ proj₁ (proj₂ (⊢↝≡ pru))⟧)
  ⊢↝Eq {φ ≡' ψ} pru = ⊢↝Eq₁ pru
  ⊢↝Eq {φ} pru = ⊢↝Eq₁ (proj₂ (proj₂ (⊢↝≡ pru)))
-}


  pleib : ∀ {ψ τ φ p} → ⊢ (ψ ≡' τ) → Tₚ ⊢ (⋀ ⟦ φ [ p := ψ ] ⟧ ≈ ⟦ φ [ p := τ ] ⟧)
  pleib {ψ} {τ} {φ} {p} pru = {!!}


  -- divagando
  ⊢↝Eq' : ∀ {φ} → (pru : ⊢ φ) → (Tₚ ⊢ (⋀ ⟦ φ ⟧ ≈ true∼)) ⊎
                                   (Σ[ φ' ∈ Formula ] (Σ[ ψ ∈ Formula ]
                                   ((Tₚ ⊢ (⋀ ⟦ φ' ⟧ ≈ ⟦ ψ ⟧)) × (φ ≡ φ' ≡' ψ))))
  ⊢↝Eq' {φ ≡' ψ} (ax ∈A) = inj₂ (φ , ψ , (⟦ ∈A ⟧ₐ , refl))
  ⊢↝Eq' {true} (ax noax)
  ⊢↝Eq' {false} (ax noax)
  ⊢↝Eq' {var p} (ax noax)
  ⊢↝Eq' {¬ φ} (ax noax)
  ⊢↝Eq' {φ /≡ φ₁} (ax noax)
  ⊢↝Eq' {φ ∧ φ₁} (ax noax)
  ⊢↝Eq' {φ ∨ φ₁} (ax noax)
  ⊢↝Eq' {φ ⇒ φ₁} (ax noax)
  ⊢↝Eq' {φ ⇐ φ₁} (ax noax)
  ⊢↝Eq' {φ} (equan {.φ} {ψ} ⊢ψ ⊢ψ≡φ) with ⊢↝Eq' ⊢ψ | ⊢↝Eq' ⊢ψ≡φ
  ... | inj₁ ⊢⋀ψ≈t | inj₁ ⊢⋀ψ≡φ≈t = inj₁ pr
    where sub₁ : Subst
          sub₁ _ 0 = ⟦ φ ⟧
          sub₁ _ 1 = true∼
          sub₁ _ n = term (inj₂ n) ⟨⟩
          ⋆₁ : Tₚ ⊢ (⋀ ⟦ φ ⟧ ≐ true∼ ≈ ⟦ φ ⟧)
          ⋆₁ = psubst axₚ₃ sub₁ ∼⟨⟩
          ⋆₂ : Tₚ ⊢ (⋀ (⟦ φ ⟧ ≐ true∼) ≈ (true∼ ≐ ⟦ φ ⟧))
          ⋆₂ = psubst axₚ₂ sub₁ ∼⟨⟩
          
          pr₁ : Tₚ ⊢ (⋀ (true∼ ≐ ⟦ φ ⟧) ≈ true∼)
          pr₁ = ptrans (psym (preemp (∼▹ ⊢⋀ψ≈t (∼▹ prefl ∼⟨⟩)) equiv)) ⊢⋀ψ≡φ≈t
          pr : Tₚ ⊢ (⋀ ⟦ φ ⟧ ≈ true∼)
          pr = ptrans (psym ⋆₁) (ptrans ⋆₂ pr₁)
  ... | inj₁ ⊢⋀ψ≈t | inj₂ (ψ' , φ' , ⊢⋀ψ'≈φ' , ψ≡φ=ψ'≡φ') =
                   inj₁ (psym (ptrans (psym ⊢⋀ψ≈t) pr))
    where pr : Tₚ ⊢ (⋀ ⟦ ψ ⟧ ≈ ⟦ φ ⟧)
          pr = subst₂ (λ φ' ψ' → Tₚ ⊢ (⋀ ⟦ φ' ⟧ ≈ ⟦ ψ' ⟧))
                      (proj₁ (cong⁻¹≡ (sym ψ≡φ=ψ'≡φ')))
                      (proj₂ (cong⁻¹≡ (sym ψ≡φ=ψ'≡φ'))) ⊢⋀ψ'≈φ'
  ... | inj₂ (ψ₁ , ψ₂ , ⊢⋀ψ₁≈ψ₂ , ψ=ψ₁≡ψ₂) | inj₁ ⊢⋀ψ≡φ≈t =
                      inj₁ {!!}
    where p₁ : Tₚ ⊢ (⋀ ((⟦ ψ₁ ⟧ ≐ ⟦ ψ₂ ⟧) ≐ ⟦ φ ⟧) ≈ ((⟦ ψ₂ ⟧ ≐ ⟦ ψ₂ ⟧) ≐ ⟦ φ ⟧))
          p₁ = preemp (∼▹ (preemp (∼▹ ⊢⋀ψ₁≈ψ₂ (∼▹ prefl ∼⟨⟩)) equiv)
                      (∼▹ prefl ∼⟨⟩)) equiv
          p₂ : Tₚ ⊢ (⋀ ((⟦ ψ₂ ⟧ ≐ ⟦ ψ₂ ⟧) ≐ ⟦ φ ⟧) ≈ true∼ )
          p₂ = ptrans (psym p₁)
                      (subst (λ φ₀ → Tₚ ⊢ (⋀ (⟦ φ₀ ⟧ ≐ ⟦ φ ⟧) ≈ true∼)) ψ=ψ₁≡ψ₂ ⊢⋀ψ≡φ≈t)
  ... | inj₂ y | inj₂ y₁ = {!!}
  ⊢↝Eq' (leib pru) = {!!}


{-
  ⊢↝Eq : ∀ {φ} → (pru : ⊢ φ) → Tₚ ⊢ (⋀ ⟦ proj₁ (⊢↝≡ pru) ⟧ ≈
                                          ⟦ proj₁ (proj₂ (⊢↝≡ pru))⟧)
  ⊢↝Eq {φ ≡' ψ} (ax x) = ⟦ x ⟧ₐ
  ⊢↝Eq {true} (ax (there (there (there (there (there (there (there (there (there (there (there (there (there ()))))))))))))))
  ⊢↝Eq {false} (ax (there (there (there (there (there (there (there (there (there (there (there (there (there ()))))))))))))))
  ⊢↝Eq {var p} (ax (there (there (there (there (there (there (there (there (there (there (there (there (there ()))))))))))))))
  ⊢↝Eq {¬ φ} (ax (there (there (there (there (there (there (there (there (there (there (there (there (there ()))))))))))))))
  ⊢↝Eq {φ /≡ φ₁} (ax (there (there (there (there (there (there (there (there (there (there (there (there (there ()))))))))))))))
  ⊢↝Eq {φ ∧ φ₁} (ax (there (there (there (there (there (there (there (there (there (there (there (there (there ()))))))))))))))
  ⊢↝Eq {φ ∨ φ₁} (ax (there (there (there (there (there (there (there (there (there (there (there (there (there ()))))))))))))))
  ⊢↝Eq {φ ⇒ φ₁} (ax (there (there (there (there (there (there (there (there (there (there (there (there (there ()))))))))))))))
  ⊢↝Eq {φ ⇐ φ₁} (ax (there (there (there (there (there (there (there (there (there (there (there (there (there ()))))))))))))))
  ⊢↝Eq {φ} (equan {.φ} {ψ} ⊢ψ ⊢ψ≡φ) = {!!}
    where ⊢true≡ψ : ⊢ (true ≡' ψ)
          ⊢true≡ψ = equan {!proj₂ (proj₂ (⊢↝≡ ⊢ψ))!} (ax (there here))
          
  ⊢↝Eq (leib pru) = {!!}
-}
