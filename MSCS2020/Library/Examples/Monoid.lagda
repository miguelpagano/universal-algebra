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
-- Definition of the theory of Monoids.
--
module Examples.Monoid where


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
open import Setoids hiding (∥_∥)
open import TermAlgebra using (Vars; module OpenTerm)
open import UnivAlgebra

open Hom

module Monoid {op-mon : List ⊤ × ⊤ → Set}
              (e      : op-mon ([] ↦ tt))
              (●     : op-mon ((tt ∷ [ tt ]) ↦ tt))
       where

  Σ-mon : Signature
  Σ-mon = record { sorts = ⊤ ; ops = op-mon }

  module Theory where

    X : Vars Σ-mon
    X ⊤ = ℕ

    open OpenTerm Σ-mon X renaming (T_〔_〕 to Terms) public
    open Equational Σ-mon

    Eq₁ : Set
    Eq₁ = Equation X tt

    Term : Set
    Term = Terms ∥ tt ∥

    module MonSmartcons where
    -- smart constructors
      _∘_ : Term → Term → Term
      φ ∘ ψ = term ● ⟨⟨ φ , ψ ⟩⟩

      x : Term
      x = term (inj₂ 0) ⟨⟩

      y : Term
      y = term (inj₂ 1) ⟨⟩

      z : Term
      z = term (inj₂ 2) ⟨⟩

      u : Term
      u = term (inj₁ e) ⟨⟩

    open MonSmartcons
    -- Axioms
    assocOp : Eq₁
    assocOp = ⋀ (x ∘ y) ∘ z ≈ (x ∘ (y ∘ z))

    unitLeft : Eq₁
    unitLeft = ⋀ u ∘ x ≈ x

    unitRight : Eq₁
    unitRight = ⋀ x ∘ u ≈ x

    pattern mon-assoc-ax = here
    pattern mon-unitL-ax = there here
    pattern mon-unitR-ax  = there (there here)

    MonTheory  : Theory X (tt ∷ tt ∷ [ tt ])
    MonTheory = assocOp ▹ (unitLeft ▹ unitRight ▹ ⟨⟩)

{- Abelian monoid (commutative monoid) -}
module AbeMonoid {op-abe-mon : List ⊤ × ⊤ → Set}
                 (e          : op-abe-mon ([] ↦ tt))
                 (●          : op-abe-mon ((tt ∷ [ tt ]) ↦ tt))
       where

  Σ-abe-mon : Signature
  Σ-abe-mon = record { sorts = ⊤ ; ops = op-abe-mon }

  open module M = Monoid {op-abe-mon} e ●

  module AbeTheory where

    open M.Theory
    open MonSmartcons
    open Equational Σ-abe-mon

    -- Commutativity
    commOp : Eq₁
    commOp = ⋀ (x ∘ y) ≈ (y ∘ x)

    AbeMonTheory : Theory X (tt ∷ tt ∷ tt ∷ tt ∷ [])
    AbeMonTheory = commOp ▹ MonTheory

module Monoids where

  data op-mon : List ⊤ × ⊤ → Set where
    e    : op-mon ([] ↦ tt)
    op   : op-mon ((tt ∷ [ tt ]) ↦ tt)

  open module M = Monoid {op-mon} e op
  open M.Theory
  open Equational Σ-mon
  e-mon : ∀ {a l A _≈_ _∘_} {e : A} →
             (m : IsMonoid {a} {l} _≈_ _∘_ e) → A
  e-mon {e = u} _ = u

  MkMonoid : ∀ {a l A _≈_ _∘_} {e : A} →
             (m : IsMonoid {a} {l} _≈_ _∘_ e) → Algebra {a} {l} Σ-mon
  MkMonoid {A = A} {_≈_} {_∘_} {eA} isMon = record
    { _⟦_⟧ₛ = λ _ → record
            { Carrier = A ; _≈_ = _≈_
            ; isEquivalence = isEquivalence
            }
    ; _⟦_⟧ₒ = (λ { e → record { _⟨$⟩_ = λ x₁ → eA
                             ; cong = λ {i} {j} _ →
                                        IsEquivalence.refl
                                        (IsSemigroup.isEquivalence
                                          (isSemigroup ))
                             }
                  ; op → record { _⟨$⟩_ = λ { (v ▹ v₁ ▹ ⟨⟩) → v ∘ v₁ }
                                ; cong = λ { (∼▹ x₁ (∼▹ x₂ ∼⟨⟩)) →
                                             ∙-cong x₁ x₂ }
                                }
                  })
    }
    where open IsMonoid isMon

  {- Each monoid is a model of our theory. -}
  MonoidModel : ∀ {a l A _≈_ _∘_} {e : A} →
                (m : IsMonoid {a} {l} _≈_ _∘_ e) → MkMonoid m ⊨T MonTheory
  MonoidModel m mon-assoc-ax θ ∼⟨⟩ =
                IsSemigroup.assoc (isSemigroup m) (θ 0) (θ 1) (θ 2)
    where open IsMonoid
  MonoidModel m mon-unitL-ax θ ∼⟨⟩ =  proj₁ (identity m) (θ 0)
    where open IsMonoid
  MonoidModel m mon-unitR-ax θ ∼⟨⟩ =  proj₂ (identity m) (θ 0)
    where open IsMonoid

  open Setoid
  {- and we can also build a monoid from a model. -}
  monFromModel : ∀ {ℓ a} {A : Algebra {ℓ} {a} Σ-mon} → A ⊨T MonTheory →
    IsMonoid (_≈_ (A ⟦ tt ⟧ₛ)) (λ x y → A ⟦ op ⟧ₒ ⟨$⟩ ⟨⟨ x , y ⟩⟩ ) (A ⟦ e ⟧ₒ ⟨$⟩ ⟨⟩)
  monFromModel {A = A} mod = record {
                 isSemigroup = record {
                   isMagma = record {
                     isEquivalence = isEquivalence (A ⟦ tt ⟧ₛ)
                                  ; ∙-cong = λ x₁ x₂ → cong (_⟦_⟧ₒ A op)
                                                             (∼▹ x₁ (∼▹ x₂ ∼⟨⟩))
                     }
                     ; assoc = λ x₁ y₁ z₁ → mod here (η x₁ y₁ z₁) ∼⟨⟩
                   }
                 ; identity = (λ x₁ → mod (there here) (λ x₂ → x₁) ∼⟨⟩)
                              , (λ x₁ → mod (there (there here)) (λ _ → x₁) ∼⟨⟩)
                 }
      where η : A ∥ tt ∥ →  A ∥ tt ∥ → A ∥ tt ∥ → Env A
            η a b c zero = a
            η a b c (suc zero) = b
            η a b c (suc (suc x₁)) = c

  module _  {a l A _≈_ _≈′_ _∘_ _∙_} {e e' : A}
               (m : IsMonoid {a} {l} _≈_ _∘_ e)
               (m' : IsMonoid {a} {l} _≈′_ _∙_ e') where
    open import Birkhoff
    open import Product

    M = MkMonoid m
    M⊨Mon = MonoidModel m
    M' = MkMonoid m'
    M'⊨Mon = MonoidModel m'
    M×M' = monFromModel {A = M ×-alg M'} modelM×M'
      where
      open ProdAlg
      open ModSemiEquationIsISP MonTheory
      modelM×M' = binProdClosed M M' M⊨Mon M'⊨Mon

-- Test that shows we can compute with the constructed product.
{-
test : _
test = {!proj₁ (IsMonoid.identity (M×M' (isMonoid m1) (isMonoid m2))) (true , false)!} -- M×M' (isMonoid m1) (isMonoid m2)
  where open import Data.Bool.Properties
        m1 = ∨-isCommutativeMonoid
        m2 = ∨-isCommutativeMonoid
        open Monoids
        open import Algebra
        open IsCommutativeMonoid
        open IsMonoid
        open import Data.Bool
        open import Data.Product
-}


{- Booleans with false and ∨ are a monoid. -}
module ∨-Monoid where
  open import Data.Bool
  open import Relation.Binary.PropositionalEquality using (setoid;refl;_≡_)
  open import Function.Equality as FE renaming (_∘_ to _∘ₛ_) hiding (setoid)

  data op-mon : List ⊤ × ⊤ → Set where
    e    : op-mon ([] ↦ tt)
    op   : op-mon ((tt ∷ [ tt ]) ↦ tt)

  open module M = Monoid {op-mon} e op
  open M.Theory

  ∨-Monₛ : ⊤ → _
  ∨-Monₛ tt = setoid Bool

  ∨-Monₒ : ∀ {ar s } → ops Σ-mon (ar , s) → (∨-Monₛ ✳ ar) ⟶ ∨-Monₛ s
  ∨-Monₒ e = record
    { _⟨$⟩_ = λ { ⟨⟩ → false };
    cong = λ { ∼⟨⟩ → refl }
    }

  ∨-Monₒ op = record { _⟨$⟩_ = ∨-fun ; cong = ∨-cong }
    where
    ∨-fun : HVec (λ _ → Bool) (tt ∷ [ tt ]) → Bool
    ∨-fun (b ▹ b' ▹ ⟨⟩) = b ∨ b'
    ∨-cong : ∀ {bs bs'} → _∼v_ {R = λ {_} → _≡_} bs bs' →
                           ∨-fun bs ≡ ∨-fun bs'
    ∨-cong (∼▹ refl (∼▹ refl ∼⟨⟩)) = refl

  ∨-Alg : Algebra Σ-mon
  ∨-Alg = record { _⟦_⟧ₛ = ∨-Monₛ ; _⟦_⟧ₒ = ∨-Monₒ }

  ∧-Monₛ : ⊤ → _
  ∧-Monₛ tt = setoid Bool

  ∧-Monₒ : ∀ {ar s } → ops Σ-mon (ar , s) → (∧-Monₛ ✳ ar) ⟶ ∧-Monₛ s
  ∧-Monₒ e = record { _⟨$⟩_ = λ { ⟨⟩  → true }; cong = λ { ∼⟨⟩ → refl }}
  ∧-Monₒ op = record { _⟨$⟩_ = ∧-fun ; cong = ∧-cong }
    where
    ∧-fun : HVec (λ _ → Bool) (tt ∷ [ tt ]) → Bool
    ∧-fun (b ▹ b' ▹ ⟨⟩) = b ∧ b'
    ∧-cong : ∀ {bs bs'} → _∼v_ {R = λ {_} → _≡_} bs bs' →
                           ∧-fun bs ≡ ∧-fun bs'
    ∧-cong (∼▹ refl (∼▹ refl ∼⟨⟩)) = refl

  ∧-Alg : Algebra Σ-mon
  ∧-Alg = record { _⟦_⟧ₛ =  ∧-Monₛ ; _⟦_⟧ₒ =  ∧-Monₒ }

  ¬-⟿ : ∨-Alg ⟿ ∧-Alg
  ¬-⟿ = λ s → record { _⟨$⟩_ = λ x → not x ; cong = λ { refl → refl }}

  ¬-cond : homCond ∨-Alg ∧-Alg ¬-⟿
  ¬-cond {.[]} {.tt} e ⟨⟩ = refl
  ¬-cond {.(tt ∷ tt ∷ [])} {.tt} op (false ▹ b' ▹ ⟨⟩) = refl
  ¬-cond {.(tt ∷ tt ∷ [])} {.tt} op (true ▹ b' ▹ ⟨⟩) = refl

  ¬-Hom : Homo ∨-Alg ∧-Alg
  ¬-Hom = record { ′_′ = ¬-⟿ ; cond = ¬-cond }

\end{code}
\end{document}

