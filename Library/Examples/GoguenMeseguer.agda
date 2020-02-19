-- Universal Algebra Library
--
-- Example taken from "Completeness of Many-sorted equational
--  logic" by Goguen and Meseguer.
--
module Examples.GoguenMeseguer where

open import Data.Bool using (true;false)
import Data.Bool as B
open import Data.Empty
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Unit hiding (setoid)
import Function as F
open import Function.Equality renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Level renaming (zero to lzero ; suc to lsuc)
open import Relation.Binary
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PropositionalEquality as PE hiding ([_])

open import Equational
open import HeterogeneousVec
open import Morphisms
open import Setoids
open import SigMorphism
open import TermAlgebra
open import UnivAlgebra


open Signature

module EqBool where

  -- The signature consists of sort bool with the operations of
  -- propositional logic, and a new sort 'a' with an operation
  -- foo : a ↦ bool.
  data sorts∼ : Set where
    bool : sorts∼
    a    : sorts∼

  data Σops∼ : List sorts∼ × sorts∼ → Set where
    t   : Σops∼ ([] ↦ bool)
    f   : Σops∼ ([] ↦ bool)
    neg : Σops∼ ([ bool ] ↦ bool)
    and∼ : Σops∼ ((bool ∷ [ bool ]) ↦ bool)
    or∼  : Σops∼ ((bool ∷ [ bool ]) ↦ bool)
    foo : Σops∼ ([ a ] ↦ bool)

  Σ∼ : Signature
  Σ∼ = record { sorts = sorts∼ ; ops = Σops∼ }

  Vars∼ : Vars Σ∼
  Vars∼ bool = ℕ
  Vars∼ a = ⊤

  Eq∼ : Set
  Eq∼ = Equation Σ∼ Vars∼ bool

  -- A formula is a term of the Term Algebra.
  Form : Set
  Form = HU (Σ∼ 〔 Vars∼ 〕) bool

  aterm : Set
  aterm = HU (Σ∼ 〔 Vars∼ 〕) a

  module Smartcons where

    ¬ : Form → Form
    ¬ φ = term neg ⟪ φ ⟫

    _∨_ : Form → Form → Form
    φ ∨ ψ = term or∼ ⟨⟨ φ , ψ ⟩⟩

    _∧_ : Form → Form → Form
    φ ∧ ψ = term and∼ ⟨⟨ φ , ψ ⟩⟩

    fu : aterm → Form
    fu aₜ = term foo ⟪ aₜ ⟫

    b : Form
    b = term (inj₂ 0) ⟨⟩

    av : aterm
    av = term (inj₂ tt) ⟨⟩

    T : Form
    T = term (inj₁ t) ⟨⟩

    F : Form
    F = term (inj₁ f) ⟨⟩

  module Theory where
    open Smartcons

    {- The theory consist of seven axioms -}
    notT : Eq∼
    notT = ⋀ ¬ T ≈ F

    notF : Eq∼
    notF = ⋀ ¬ F ≈ T
    3exc : Eq∼
    3exc = ⋀ b ∨ (¬ b) ≈ T

    b∧¬b : Eq∼
    b∧¬b = ⋀ b ∧ (¬ b) ≈ F

    idem∧ : Eq∼
    idem∧ = ⋀ b ∧ b ≈ b

    idem∨ : Eq∼
    idem∨ = ⋀ b ∨ b ≈ b

    fooax : Eq∼
    fooax = ⋀ fu av ≈ ¬ (fu av)

    Th : Theory Σ∼ Vars∼ (replicate 7 bool)
    Th = notT ▹ notF ▹ 3exc ▹ b∧¬b ▹ idem∧ ▹ idem∨ ▹ fooax ▹ ⟨⟩

    pattern ax₁ = here
    pattern ax₂ = there here
    pattern ax₃ = there (there here)
    pattern ax₄ = there (there (there here))
    pattern ax₅ = there (there (there (there here)))
    pattern ax₆ = there (there (there (there (there here))))
    pattern ax₇ = there (there (there (there (there (there here)))))
    pattern noax = there (there (there (there (there (there (there ()))))))

  module Proof where
    open Theory
    open EqR (⊢RSetoid Th bool)
    open Subst {Σ∼} {Vars∼}
    open Equation
    open Smartcons
    open TermAlgebra


    {- We can prove T ≈ F -}
    t≈f : Th ⊢ (⋀ T ≈ F)
    t≈f =
      begin
        T
      ≈⟨ psym (ax₃ ∣ σ₁) ⟩
        (fu av ∨ (¬ (fu av)))
      ≈⟨ preemp ∼⟨⟨ prefl , psym (ax₇ ∣ idSubst) ⟩⟩∼ ⟩
        (fu av ∨ fu av)
      ≈⟨ ax₆ ∣ σ₁ ⟩
        fu av
      ≈⟨ psym (ax₅ ∣ σ₁) ⟩
        (fu av ∧ fu av)
      ≈⟨ preemp ∼⟨⟨ prefl , ax₇ ∣ idSubst ⟩⟩∼ ⟩
        (fu av ∧ (¬ (fu av)))
      ≈⟨ ax₄ ∣ σ₁ ⟩
        F
      ∎
      where σ₁ : Subst
            σ₁ {bool} 0 = fu av
            σ₁ {bool} (suc x) = term (inj₂ x) ⟨⟩
            σ₁ {a} tt = term (inj₂ tt) ⟨⟩



  {- Now we try to prove true ≡ false via soundness of equational logic -}
  module NotCorrectness where

    isorts : sorts Σ∼ → Setoid _ _
    isorts bool = PE.setoid B.Bool
    isorts a = PE.setoid ⊥

    iops : ∀ {ar s} → (op : ops Σ∼ (ar ↦ s)) → isorts ✳ ar ⟶ isorts s
    iops t = record { _⟨$⟩_ = λ _ → true ; cong = λ _ → PE.refl }
    iops f = record { _⟨$⟩_ = λ _ → false ; cong = λ _ → PE.refl }
    iops neg = record { _⟨$⟩_ = λ { ⟪ b ⟫ → B.not b } ;
                        cong = λ { {b₀ ▹ ⟨⟩} {b₁ ▹ ⟨⟩} (∼▹ b₀≡b₁ _) → PE.cong B.not b₀≡b₁ } }
    iops and∼ = record { _⟨$⟩_ = λ { ⟨⟨ b , b' ⟩⟩ → b B.∧ b' } ;
                      cong = λ { {⟨⟨ b₀ , b₀' ⟩⟩} {⟨⟨ b₁ , b₁' ⟩⟩}
                                 (∼▹ b₀≡b₁ (∼▹ b₀'≡b₁' ∼⟨⟩)) →
                                                     PE.cong₂ B._∧_ b₀≡b₁ b₀'≡b₁' } }
    iops or∼ = record { _⟨$⟩_ = λ { ⟨⟨ b , b' ⟩⟩ → b B.∨ b' } ;
                      cong = λ { {⟨⟨ b₀ , b₀' ⟩⟩} {⟨⟨ b₁ , b₁' ⟩⟩}
                                 (∼▹ b₀≡b₁ (∼▹ b₀'≡b₁' ∼⟨⟩)) →
                                                     PE.cong₂ B._∨_ b₀≡b₁ b₀'≡b₁' } }
    iops foo = record { _⟨$⟩_ = λ { (() ▹ ⟨⟩) }
                      ; cong = λ { {() ▹ ⟨⟩} {noel₂ ▹ ⟨⟩} (∼▹ ₁≡₂ x) } }

    model : Algebra Σ∼
    model = record { _⟦_⟧ₛ =  isorts ; _⟦_⟧ₒ = iops }

    open Theory


    sat₁ : model ⊨ notT
    sat₁ θ _ = PE.refl

    sat₂ : model ⊨ notT
    sat₂ θ _ = PE.refl

    sat₃ : model ⊨ 3exc
    sat₃ θ _ with θ {bool} 0
    sat₃ θ x | false = PE.refl
    sat₃ θ x | true = PE.refl

    sat₄ : model ⊨ b∧¬b
    sat₄ θ _ with θ {bool} 0
    sat₄ θ x | false = PE.refl
    sat₄ θ x | true = PE.refl

    sat₅ : model ⊨ idem∧
    sat₅ θ _ with θ {bool} 0
    sat₅ θ x | false = PE.refl
    sat₅ θ x | true = PE.refl

    sat₆ : model ⊨ idem∨
    sat₆ θ _ with θ {bool} 0
    sat₆ θ x | false = PE.refl
    sat₆ θ x | true = PE.refl

    sat₇ : model ⊨ fooax
    sat₇ θ ∼⟨⟩ with (θ {a} tt)
    sat₇ θ ∼⟨⟩ | ()


    ismodel : model ⊨T Th
    ismodel = sat
      where sat : {s : sorts∼} {e : Equation _ Vars∼ s} → e ∈ Th → model ⊨ e
            sat ax₁ = sat₁
            sat ax₂ = λ θ _ → PE.refl
            sat ax₃ = sat₃
            sat ax₄ = sat₄
            sat ax₅ = sat₅
            sat ax₆ = sat₆
            sat ax₇ = sat₇
            sat noax


    {- We could use soundness to prove this absurd. But we should
       give an environment from a non-empty set of variables to
       an empty carrier set. -}
    -- You can uncomment the next function and try to fill the hole.
{-
    abs : true ≡ false
    abs = soundness t≈f model ismodel env ∼⟨⟩
      where open Proof
            env : Env Vars∼ model
            env {bool} v = true
            -- We cannot give an element of ⊥
            env {a} v = {!!}
-}

