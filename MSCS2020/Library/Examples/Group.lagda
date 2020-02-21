\documentclass{article}
\usepackage{agda}
\usepackage{amsmath}
\usepackage{mathpartir}


%include agda.fmt
%include unicode.fmt

\begin{document}
\begin{code}

-- Universal Algebra Library
--
-- Definition of the theory of Groups, extending the theory of
-- Monoids.
--
module Examples.Group where

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
import Equational
open import HeterogeneousVec renaming (map to vmap)
open import Morphisms
open import Product
open import TermAlgebra
open import UnivAlgebra

open import Examples.Monoid

open Hom


module Group {op-grp : List ⊤ × ⊤ → Set}
             (e      : op-grp ([] ↦ tt))
             (_⁻¹    : op-grp ([ tt ] ↦ tt))
             (●     : op-grp ((tt ∷ [ tt ]) ↦ tt))
       where
  open module M = Monoid {op-grp} e ●

  Σ-grp : Signature
  Σ-grp = record { sorts = ⊤ ; ops = op-grp }

  module GrpTheory where
    open M.Theory hiding (HU;term)

    module OTG = OpenTerm Σ-grp X renaming (T_〔_〕 to GTerms)
    open OTG
    open Equational Σ-grp
    Eq-grp : Set
    Eq-grp = Equation X tt

    Term-grp : Set
    Term-grp = GTerms ∥ tt ∥

    module GrpSmartcons where
    -- smart constructors
      _∘_ : Term-grp → Term-grp → Term-grp
      a ∘ b = term ● ⟨⟨ a , b ⟩⟩

      _⁻ : Term-grp → Term-grp
      a ⁻ = term _⁻¹ (⟪ a ⟫)

      x : Term-grp
      x = term (inj₂ 0) ⟨⟩

      u : Term-grp
      u = term (inj₁ e) ⟨⟩

    open GrpSmartcons
    -- Axioms
    invElemRight : Eq-grp
    invElemRight = ⋀ (x ∘ (x ⁻)) ≈ u

    invElemLeft : Eq-grp
    invElemLeft = ⋀ ((x ⁻) ∘ x) ≈ u

    pattern grp-invR-ax = here
    pattern grp-invL-ax = there here
    pattern grp-ass-ax  = there (there here)
    pattern grp-unitL-ax = there (there (there here ))
    pattern grp-unitR-ax = there (there (there (there here)))

    GrpTheory : Theory X (tt ∷ tt ∷ tt ∷ tt ∷ [ tt ])
    GrpTheory = invElemRight ▹ (invElemLeft ▹ MonTheory)

    module _ where
      open Provable-Equivalence GrpTheory
      open EqR (⊢-≈Setoid tt)
      open OTG.Subst

      {- unit is its own inverse. -}
      p₁ : GrpTheory ⊢ (⋀ (u ⁻) ≈ u)
      p₁ = begin ((u ⁻))
           ≈⟨  psym (psubst grp-unitL-ax (λ x₁ → (u ⁻)) ∼⟨⟩) ⟩
           ((u ∘ (u ⁻)))
           ≈⟨ psubst grp-invR-ax (λ x₁ → u) ∼⟨⟩ ⟩
           u
           ∎

      inv-inv : GrpTheory ⊢ (⋀ x ≈ ((x ⁻) ⁻) if「 [] 」 (⟨⟩ , ⟨⟩))
      inv-inv = begin x
                ≈⟨ psym (psubst grp-unitR-ax (λ x → term (inj₂ x) ⟨⟩) ∼⟨⟩) ⟩
                (x ∘ u)
                ≈⟨ preemp (∼▹ prefl (∼▹ (psym (psubst grp-invR-ax
                                              (λ _ → x ⁻) ∼⟨⟩)) ∼⟨⟩)) ⟩
                (x ∘ ((x ⁻) ∘ (((x ⁻)) ⁻)))
                ≈⟨ psym (psubst grp-ass-ax σ ∼⟨⟩) ⟩
                ((x ∘ (x ⁻)) ∘ ((x ⁻) ⁻))
                ≈⟨ preemp (∼▹ (psubst grp-invR-ax (λ _ → x) ∼⟨⟩)
                          (∼▹ prefl ∼⟨⟩)) ⟩
                (u ∘ ((x ⁻) ⁻))
                ≈⟨ psubst grp-unitL-ax (λ _ → (x ⁻) ⁻) ∼⟨⟩ ⟩
                ((x ⁻) ⁻)
                ∎
         where σ : Subst
               σ zero = x
               σ (suc zero) = x ⁻
               σ (suc (suc zero)) = (x ⁻) ⁻
               σ v = term (inj₂ v) ⟨⟩

{- Abelian group -}
module AbeGroup {op-abe-grp : List ⊤ × ⊤ → Set}
                (e      : op-abe-grp ([] ↦ tt))
                (_⁻¹    : op-abe-grp ([ tt ] ↦ tt))
                (bop    : op-abe-grp ((tt ∷ [ tt ]) ↦ tt))
       where

       Σ-abe-grp : Signature
       Σ-abe-grp = record { sorts = ⊤ ; ops = op-abe-grp }

       open module G = Group {op-abe-grp} e _⁻¹ bop

       module AbeGrpTheory where

         open M.Theory
         open G.GrpTheory
         open Equational Σ-abe-grp

         Eq-abe-grp : Set
         Eq-abe-grp = Eq-grp

         Term-abe-grp : Set
         Term-abe-grp = Term-grp

         module AbeGrpSmartcons where
           y : Term-grp
           y = term (inj₂ 1) ⟨⟩

         open GrpSmartcons
         open AbeGrpSmartcons
         -- Commutativity
         commOp : Eq-abe-grp
         commOp = ⋀ (x ∘ y) ≈ (y ∘ x)

         AbeGrpTheory : Theory X (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [ tt ])
         AbeGrpTheory = commOp ▹ GrpTheory

module Groups where

  data op-grp : List ⊤ × ⊤ → Set where
    e    : op-grp ([] ↦ tt)
    _⁻¹  : op-grp ([ tt ] ↦ tt)
    op   : op-grp ((tt ∷ [ tt ]) ↦ tt)

  open module G = Group {op-grp} e _⁻¹ op
  open G.GrpTheory
  open M.Theory
  open Monoids
  open Equational Σ-grp
  {- Each group is a model of our theory. -}
  MkGroup : ∀ {l₀ l₁ A _≈_ bop uop} {e : A} →
             (g : IsGroup {l₀} {l₁} _≈_ bop e uop) → Algebra {l₀} {l₁} G.Σ-grp
  MkGroup {A = A} {_≈_} {bop} {uop} {eA} isGrp =
       record { _⟦_⟧ₛ = λ _ → record { Carrier = A
                                     ; _≈_ = _≈_
                                     ; isEquivalence = isEquivalence
                                     }
              ; _⟦_⟧ₒ = λ { e → record { _⟨$⟩_ = λ x → eA
                                       ; cong = λ x → IsEquivalence.refl
                                                  (IsMonoid.isEquivalence
                                                  isMonoid)
                                       }
                         ; _⁻¹ → record { _⟨$⟩_ = λ { ⟪ v ⟫ → uop v}
                                        ; cong = λ { (∼▹ x ∼⟨⟩) → ⁻¹-cong x }
                                        }
                        ; op → record { _⟨$⟩_ = λ { (v ▹ v₁ ▹ ⟨⟩) → bop v v₁ }
                                         ; cong = λ { (∼▹ x₁ (∼▹ x₂ ∼⟨⟩)) →
                                                      ∙-cong x₁ x₂ }
                                         }
                         }
             }
             where open IsGroup isGrp

  {- Each monoid is a model of our theory. -}
  GroupModel : ∀ {l₀ l₁ A _≈_ bop uop} {e : A} →
             (g : IsGroup {l₀} {l₁} _≈_ bop e uop) → MkGroup g ⊨T GrpTheory
  GroupModel m grp-invR-ax  θ eqs = inverseʳ m (θ 0)
    where open IsGroup
  GroupModel m grp-invL-ax  θ eqs = inverseˡ m (θ 0)
    where open IsGroup
  GroupModel m grp-ass-ax   θ eqs = MonoidModel (isMonoid m) mon-assoc-ax θ ∼⟨⟩
    where open IsGroup
  GroupModel m grp-unitL-ax θ eqs = MonoidModel (isMonoid m) mon-unitL-ax θ ∼⟨⟩
    where open IsGroup
  GroupModel m grp-unitR-ax θ eqs = MonoidModel (isMonoid m) mon-unitR-ax θ ∼⟨⟩
    where open IsGroup

  open Setoid

  {- and we can also build a group from a model. -}
  grpFromModel : ∀ {ℓ a} {A : Algebra {ℓ} {a} Σ-grp} → A ⊨T GrpTheory →
    IsGroup (_≈_ (A ⟦ tt ⟧ₛ))
            (λ x y → A ⟦ op ⟧ₒ ⟨$⟩ ⟨⟨ x , y ⟩⟩ ) (A ⟦ e ⟧ₒ ⟨$⟩ ⟨⟩)
            (λ x → (A ⟦ _⁻¹ ⟧ₒ) ⟨$⟩ ⟪ x ⟫)
  grpFromModel {A = A} mod = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = isEquivalence (A ⟦ tt ⟧ₛ)
          ; ∙-cong = λ x₁ x₂ → cong (_⟦_⟧ₒ A op) (∼▹ x₁ (∼▹ x₂ ∼⟨⟩))
          }
        ; assoc = λ x₁ y₁ z₁ → mod grp-ass-ax (η x₁ y₁ z₁) ∼⟨⟩
        }
      ; identity = (λ x₁ → mod grp-unitL-ax (λ x₂ → x₁) ∼⟨⟩)
                           , (λ x₁ → mod grp-unitR-ax (λ _ → x₁) ∼⟨⟩)
      }
    ; inverse = ( (λ x → mod grp-invL-ax (λ x₂ → x) ∼⟨⟩)
                       , (λ x → mod grp-invR-ax (λ x₂ → x) ∼⟨⟩)
                  )
    ; ⁻¹-cong = λ {x} {y} x≈y → cong (A ⟦ _⁻¹ ⟧ₒ) (∼▹ x≈y ∼⟨⟩)
    }
    where η :  A ∥ tt ∥ → A ∥ tt ∥ → A ∥ tt ∥ → OTG.Env A
          η a b c zero = a
          η a b c (suc zero) = b
          η a b c (suc (suc x₁)) = c

\end{code}
\end{document}
