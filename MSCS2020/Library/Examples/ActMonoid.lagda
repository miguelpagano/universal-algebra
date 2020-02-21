\documentclass{article}
\usepackage{agda}
\usepackage{amsmath}
\usepackage{mathpartir}


%include agda.fmt
%include unicode.fmt

\begin{document}
\begin{code}

{- The example of monoid acting on a set is one of the
examples given by Birkhoff and Lipton. -}
module Examples.ActMonoid where

open import UnivAlgebra
open import Equational
open import Morphisms
open import SigMorphism
open import Data.Unit hiding (setoid)
open import Data.List
open import Data.Product
open import Data.Nat
open import Data.Sum
open import HeterogeneousVec
open import Setoids

open import Relation.Binary

open Signature
open Hom

open import Level
open Setoid using (_≈_)
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (setoid;refl;_≡_)
open import Function.Equality as FE renaming (_∘_ to _∘ₛ_) hiding (setoid)

data actMonₛ : Set where mon set : actMonₛ

data op-actMon : List actMonₛ × actMonₛ → Set where
  e  : op-actMon ([] , mon)
  *  : op-actMon (mon ∷ [ mon ] , mon)
  ∙  : op-actMon (mon ∷ [ set ] , set)


Σ-actMon : Signature
sorts Σ-actMon = actMonₛ
ops   Σ-actMon = op-actMon

ℕ-actₛ : actMonₛ → Setoid Level.zero Level.zero
ℕ-actₛ mon = setoid ℕ
ℕ-actₛ set = setoid (List ℕ)

open import Data.Nat using (_*_)
ℕ-actₒ : ∀ {ar s } → ops Σ-actMon (ar , s) → (ℕ-actₛ ✳ ar) ⟶ ℕ-actₛ s
_⟨$⟩_ (ℕ-actₒ e) _ = 1
_⟨$⟩_ (ℕ-actₒ *) = {!$ⁿ_!} -- ?(_*_ $ⁿ_
_⟨$⟩_ (ℕ-actₒ ∙) (ℕ.zero ▹ xs ▹ ⟨⟩) = []
_⟨$⟩_ (ℕ-actₒ ∙) (ℕ.suc m ▹ xs ▹ ⟨⟩) = xs ++ ((ℕ-actₒ ∙) ⟨$⟩ (m ▹ xs ▹ ⟨⟩))

cong  (ℕ-actₒ e) _ = refl
cong  (ℕ-actₒ *) (∼▹ refl (∼▹ refl ∼⟨⟩)) = refl
cong  (ℕ-actₒ ∙) (∼▹ refl (∼▹ refl ∼⟨⟩)) = refl

\end{code}
\end{document}

