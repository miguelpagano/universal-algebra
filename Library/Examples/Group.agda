{- Definition of the theory of Groups, extending theory of Monoids. -}
module Examples.Group where

open import UnivAlgebra
open import Equational
open import Morphisms
open import SigMorphism
open import Data.Unit hiding (setoid)
open import Data.List
open import Data.Product
open import Data.Nat
open import Data.Sum
open import HeterogeneousVec renaming (map to vmap)
open import Setoids

open Signature
open Algebra
open Hom

open import Examples.Monoid

module Group {op-grp : List ⊤ × ⊤ → Set}
             (e      : op-grp ([] ↦ tt))
             (_⁻¹    : op-grp ([ tt ] ↦ tt))
             (●     : op-grp ((tt ∷ [ tt ]) ↦ tt))
       where
       open module M = Monoid {op-grp} e ●

       Σ-grp : Signature
       Σ-grp = record { sorts = ⊤ ; ops = op-grp }

       module GrpTheory where
         open M.Theory
         open import TermAlgebra

         Eq-grp : Set
         Eq-grp = Equation Σ-grp X tt

         -- A formula is a term of the Term Algebra
         Form-grp : Set
         Form-grp = HU (Σ-grp 〔 X 〕) tt

         module GrpSmartcons where
         -- smart constructors
           _∘_ : Form-grp → Form-grp → Form-grp
           a ∘ b = term ● ⟨⟨ a , b ⟩⟩

           _⁻ : Form-grp → Form-grp
           a ⁻ = term _⁻¹ (⟪ a ⟫)

           x : Form-grp
           x = term (inj₂ 0) ⟨⟩

           u : Form-grp
           u = term (inj₁ e) ⟨⟩

         open GrpSmartcons
         -- Axioms
         invElemLeft : Eq-grp
         invElemLeft = ⋀ (x ∘ (x ⁻)) ≈ u

         invElemRight : Eq-grp
         invElemRight = ⋀ ((x ⁻) ∘ x) ≈ u

         GrpTheory : Theory Σ-grp X (tt ∷ tt ∷ tt ∷ tt ∷ [ tt ])
         GrpTheory = invElemRight ▹ (invElemLeft ▹ MonTheory)

         module Props where
         open import Relation.Binary.EqReasoning (⊢RSetoid GrpTheory tt)
         open Subst {Σ-grp} {X}

         pattern invR-ax = here
         pattern invL-ax = there here
         pattern ass-ax  = there (there here)
         pattern unitL-ax = there (there (there here ))
         pattern unitR-ax = there (there (there (there here)))

         {- unit is its own inverse. -}
         p₁ : GrpTheory ⊢ (⋀ (u ⁻) ≈ u)
         p₁ = begin ((u ⁻))
              ≈⟨  psym (psubst unitL-ax (λ x₁ → (u ⁻)) ∼⟨⟩) ⟩
              ((u ∘ (u ⁻)))
              ≈⟨ psubst invL-ax (λ x₁ → u) ∼⟨⟩ ⟩
              u
              ∎

         inv-inv : GrpTheory ⊢ (⋀ x ≈ ((x ⁻) ⁻) if「 [] 」 (⟨⟩ , ⟨⟩))
         inv-inv = begin x
                   ≈⟨ psym (psubst unitR-ax (λ x → term (inj₂ x) ⟨⟩) ∼⟨⟩) ⟩
                   (x ∘ u)
                   ≈⟨ preemp (∼▹ prefl (∼▹ (psym (psubst invL-ax
                                                (λ _ → x ⁻) ∼⟨⟩)) ∼⟨⟩)) ⟩
                   (x ∘ ((x ⁻) ∘ (((x ⁻)) ⁻)))
                   ≈⟨ psym (psubst ass-ax σ ∼⟨⟩) ⟩
                   ((x ∘ (x ⁻)) ∘ ((x ⁻) ⁻))
                   ≈⟨ preemp (∼▹ (psubst invL-ax (λ _ → x) ∼⟨⟩) (∼▹ prefl ∼⟨⟩)) ⟩
                   (u ∘ ((x ⁻) ⁻))
                   ≈⟨ psubst unitL-ax (λ _ → (x ⁻) ⁻) ∼⟨⟩ ⟩
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

         open import TermAlgebra

         Eq-abe-grp : Set
         Eq-abe-grp = Eq-grp

         Form-abe-grp : Set
         Form-abe-grp = Form-grp

         module AbeGrpSmartcons where
           y : Form-grp
           y = term (inj₂ 1) ⟨⟩

         open GrpSmartcons
         open AbeGrpSmartcons
         -- Commutativity
         commOp : Eq-abe-grp
         commOp = ⋀ (x ∘ y) ≈ (y ∘ x)

         AbeGrpTheory : Theory Σ-abe-grp X (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [ tt ])
         AbeGrpTheory = commOp ▹ GrpTheory

module Groups where

  data op-grp : List ⊤ × ⊤ → Set where
    e    : op-grp ([] ↦ tt)
    _⁻¹  : op-grp ([ tt ] ↦ tt)
    op   : op-grp ((tt ∷ [ tt ]) ↦ tt)

  Σ-grp : Signature
  Σ-grp = record { sorts = ⊤ ; ops = op-grp }
