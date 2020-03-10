------------------------------------------------------------
-- Universal Algebra Library
--
-- Lattices as an equational theory.
------------------------------------------------------------

open import Data.List
open import Data.Unit hiding (setoid)
open import Examples.Monosorted
module Examples.Lattice (lattice-ops : ms-ops)
                        (∨-op ∧-op : lattice-ops binary) where

open import Data.Bool
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Sum
import Function as F
open import Function.Equality renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Level renaming (zero to lzero ; suc to lsuc)
open import Reflection
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

open EqTheory lattice-ops

LTerm : Set
LTerm = ms-Term

_∧'_ _∨'_ : ms-Term → ms-Term → ms-Term
unquoteDef _∨'_ = binary-smart _∨'_ (var 3 [])
unquoteDef _∧'_ = binary-smart _∧'_ (var 2 [])

assoc-meet assoc-join : Eq
unquoteDef assoc-meet = assoc-op assoc-meet (quote _∨'_) (quote X) (quote 𝓿x) (quote 𝓿y) (quote 𝓿z)
unquoteDef assoc-join = assoc-op assoc-join (quote _∧'_) (quote X) (quote 𝓿x) (quote 𝓿y) (quote 𝓿z)

comm-meet comm-join : Eq
unquoteDef comm-meet = comm-op comm-meet (quote _∨'_) (quote X) (quote 𝓿x) (quote 𝓿y)
unquoteDef comm-join = comm-op comm-join (quote _∧'_) (quote X) (quote 𝓿x) (quote 𝓿y)

idemp-meet idemp-join : Eq
unquoteDef idemp-meet = idemp-op idemp-meet (quote _∨'_) (quote X) (quote 𝓿x)
unquoteDef idemp-join = idemp-op idemp-join (quote _∧'_) (quote X) (quote 𝓿x)

abs-meet abs-join : Eq
unquoteDef abs-meet = absorption-op abs-meet (quote _∨'_) (quote _∧'_) (quote X) (quote 𝓿x) (quote 𝓿y)
unquoteDef abs-join = absorption-op abs-join (quote _∧'_) (quote _∨'_) (quote X) (quote 𝓿x) (quote 𝓿y)

lattice-theory :  Theory (replicate 8 tt)
lattice-theory = assoc-meet ▹ assoc-join ▹ comm-meet ▹ comm-join ▹ idemp-meet ▹ idemp-join ▹ abs-meet ▹ abs-join ▹ ⟨⟩
