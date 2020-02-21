\documentclass{article}
\usepackage{agda}
\usepackage{amsmath}
\usepackage{mathpartir}


%include agda.fmt
%include unicode.fmt

\begin{document}
\begin{code}

module Signature where

open import Relation.Binary hiding (Total)
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Nat renaming (_⊔_ to _⊔ₙ_)
open import Data.Product renaming (map to pmap)
open import Function as F
open import Function.Equality as FE renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Data.Bool renaming (_≟_ to _≟b_)
open import Data.List renaming (map to lmap)
open import Relation.Binary.PropositionalEquality as PE hiding ( Reveal_·_is_;[_];isEquivalence)

open import Data.Fin hiding (_+_)

import Relation.Binary.EqReasoning as EqR

open import HeterogeneousVec

pattern _↦_ ar s = (ar , s)

open Setoid
open import Setoids

record Signature {sorts : Set} : Set₁ where 
  field
    ops : (List sorts) × sorts → Set

  Arity : Set
  Arity = List sorts

  Type : Set
  Type = List sorts × sorts

open Signature ⦃...⦄
open import Data.Sum

{- Blend of operations. This is enough for pebble inheritance.  -}
⊎-sig : ∀ {sorts} → Signature { sorts } → Signature { sorts } → Signature { sorts }
⊎-sig {sorts} sig sig' = record { ops = λ ty → ops ⦃ sig ⦄ ty  ⊎ ops ⦃ sig' ⦄ ty }

{- It is conceivable a more general form of merging of
  signatures with disjoint sorts. 

⊎-sig' : ∀ {s s'} → Signature { s } → Signature { s' } → Signature { s ⊎ s' }

It would be a bit awkward, however, to work out the details (basically
the set of operations of a given type (ar , s) is empty if there is
some element in ar which comes from the incorrect side; e.g. s ≡ inj₁ a and ar ≡ [ inj₂ b ]. 

-}


module FormalTerm { sorts }{ Σ : Signature { sorts } } where

 data _⊩_  (ar' : Arity ⦃ Σ ⦄) : (sorts) → Set where
   #   : (n : Fin (length ar')) → ar' ⊩ (ar' ‼ n)
   _∣$∣_ : ∀ {ar s} → ops ⦃ Σ ⦄ (ar , s) → 
               HVec (ar' ⊩_) ar → ar' ⊩ s

record  _↝_ { sorts sorts' } (Σₛ : Signature { sorts }) (Σₜ : Signature { sorts' }) : Set where
 open FormalTerm { sorts' } {Σₜ}
 field
  ↝ₛ : sorts → sorts'
  ↝ₒ : ∀ {ar s}  → ops ⦃ Σₛ ⦄ (ar , s) → lmap ↝ₛ ar ⊩ ↝ₛ s


\end{code}
\end{document}

