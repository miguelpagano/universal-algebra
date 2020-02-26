-------------------------------------------------------------
-- Universal Algebra Library
--
-- Conveniences for declaring monosorted equational theories.
-------------------------------------------------------------

module Examples.Monosorted where
open import Level renaming (suc to sucℓ) using (0ℓ)
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Unit

ms-sorts : Set
ms-sorts = ⊤

ms-sort : ms-sorts
ms-sort = tt

ms-type : Set
ms-type = List ms-sorts × ms-sorts

ms-ops : Set (sucℓ 0ℓ)
ms-ops = ms-type → Set

n-ary : ℕ → ms-type
n-ary n = replicate n tt , tt

constant : ms-type
constant = n-ary 0

unary : ms-type
unary = n-ary 1

binary : ms-type
binary = n-ary 2

ternary : ms-type
ternary = n-ary 3
