module Ejemplos.Logic where

open import UnivAlgebra
open import Relation.Binary
open import Data.Product renaming (map to pmap)
open import Data.Nat
open import Data.Bool
open import Level renaming (suc to lsuc ; zero to lzero)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open import Data.String hiding (setoid)
open import Function
open import Function.Equality renaming (_∘_ to _∘ₛ_) hiding (setoid;cong)
open import Data.List
open import Data.Maybe hiding (setoid ; map)
open import AlgTransf
open import Data.Fin hiding (_+_ ; #_)
open import VecH


Var : Set
Var = String




{- Traducción de lógica proposicional con todos los conectores
   a proposicional con pocos conectores -}

{- Source language -}
data Sₛ : Sorts where
  bool : Sₛ

data Fₛ : Funcs Sₛ where
  varₛ   : (v : Var) → Fₛ ([] , bool)
  trueₛ  : Fₛ ([] , bool)
  falseₛ : Fₛ ([] , bool)
  impl  : Fₛ (bool ∷ [ bool ] , bool)
  equiv : Fₛ (bool ∷ [ bool ] , bool)
  andₛ   : Fₛ (bool ∷ [ bool ] , bool)
  orₛ    : Fₛ (bool ∷ [ bool ] , bool)
  negₛ   : Fₛ ([ bool ] , bool)

Σₛ : Signature
Σₛ = record { sorts = Sₛ ; funcs = Fₛ }

PropAlgₛ : Algebra Σₛ
PropAlgₛ = ∣T∣ Σₛ

-- Semantics
State : Set
State = Var → Bool

iSₛ : ISorts Σₛ
iSₛ bool = State →-setoid Bool

open Signature
open Setoid
open Algebra


_⟹_ : Bool → Bool → Bool
p ⟹ q = not p ∨ q

_≡b_ : Bool → Bool → Bool
p ≡b q = (p ⟹ q) ∧ (q ⟹ p)


ifₛ : ∀ {ar} {s} → (f : funcs Σₛ (ar , s)) → VecH Sₛ (Carrier ∘ iSₛ) ar →
                   Carrier (iSₛ s)
ifₛ (varₛ v) ⟨⟩ = λ σ → σ v
ifₛ trueₛ ⟨⟩ = λ _ → true
ifₛ falseₛ ⟨⟩ = λ _ → false
ifₛ impl (v ▹ v₁ ▹ ⟨⟩) = λ σ → v σ ⟹ v₁ σ
ifₛ equiv (v ▹ v₁ ▹ ⟨⟩) = λ σ → v σ ≡b v₁ σ
ifₛ andₛ (v ▹ v₁ ▹ ⟨⟩) = λ σ → v σ ∧ v₁ σ
ifₛ orₛ (v ▹ v₁ ▹ ⟨⟩) = λ σ → v σ ∨ v₁ σ
ifₛ negₛ (v ▹ ⟨⟩) = λ σ → not (v σ)

ifcong : ∀ {ar} {s} → (f : funcs Σₛ (ar , s)) →
           {vs₀ vs₁ : VecH Sₛ (Carrier ∘ iSₛ) ar} →
           _∼v_ {R = _≈_ ∘ iSₛ} vs₀ vs₁ →
           _≈_ (iSₛ s) (ifₛ f vs₀) (ifₛ f vs₁)
ifcong (varₛ v) ∼⟨⟩ = λ _ → PropEq.refl
ifcong trueₛ ∼⟨⟩ = λ _ → PropEq.refl
ifcong falseₛ ∼⟨⟩ = λ _ → PropEq.refl
ifcong impl (∼▹ x (∼▹ x₁ ∼⟨⟩)) = λ σ → cong₂ _⟹_ (x σ) (x₁ σ)
ifcong equiv (∼▹ x (∼▹ x₁ ∼⟨⟩)) = λ σ → cong₂ _≡b_ (x σ) (x₁ σ)
ifcong andₛ (∼▹ x (∼▹ x₁ ∼⟨⟩)) = λ σ → cong₂ _∧_ (x σ) (x₁ σ)
ifcong orₛ (∼▹ x (∼▹ x₁ ∼⟨⟩)) = λ σ → cong₂ _∨_ (x σ) (x₁ σ)
ifcong negₛ (∼▹ x ∼⟨⟩) = λ σ → cong not (x σ)

iFₛ : ∀ {ty} → (f : funcs Σₛ ty) → IFuncs Σₛ ty iSₛ
iFₛ f = record { _⟨$⟩_ = ifₛ f ; cong = ifcong f }

Semₛ : Algebra Σₛ
Semₛ = iSₛ ∥ iFₛ

hSemₛ : Homomorphism PropAlgₛ Semₛ
hSemₛ = ∣T∣ₕ Semₛ

{- Target language -}
Sₜ : Sorts
Sₜ = Sₛ

data Fₜ : Funcs Sₜ where
  varₜ   : (v : Var) → Fₜ ([] , bool)
  falseₜ : Fₜ ([] , bool)
  orₜ    : Fₜ (bool ∷ [ bool ] , bool)
  negₜ   : Fₜ ([ bool ] , bool)


Σₜ : Signature
Σₜ = record { sorts = Sₜ ; funcs = Fₜ }

PropAlgₜ : Algebra Σₜ
PropAlgₜ = ∣T∣ Σₜ

-- Semantics
iSₜ : ISorts Σₜ
iSₜ bool = State →-setoid Bool


ifₜ : ∀ {ar} {s} → (f : funcs Σₜ (ar , s)) → VecH Sₜ (Carrier ∘ iSₜ) ar →
                   Carrier (iSₜ s)
ifₜ (varₜ v) ⟨⟩ = λ σ → σ v
ifₜ falseₜ ⟨⟩ = λ _ → false
ifₜ orₜ (v ▹ v₁ ▹ ⟨⟩) = λ σ → v σ ∨ v₁ σ
ifₜ negₜ (v ▹ ⟨⟩) = λ σ → not (v σ)

ifcongₜ : ∀ {ar} {s} → (f : funcs Σₜ (ar , s)) →
           {vs₀ vs₁ : VecH Sₜ (Carrier ∘ iSₜ) ar} →
           _∼v_ {R = _≈_ ∘ iSₜ} vs₀ vs₁ →
           _≈_ (iSₜ s) (ifₜ f vs₀) (ifₜ f vs₁)
ifcongₜ (varₜ v) ∼⟨⟩ = λ x → PropEq.refl
ifcongₜ falseₜ ∼⟨⟩ = λ x → PropEq.refl
ifcongₜ orₜ (∼▹ x (∼▹ x₁ ∼⟨⟩)) = λ σ → cong₂ _∨_ (x σ) (x₁ σ)
ifcongₜ negₜ (∼▹ x ∼⟨⟩) = λ σ → cong not (x σ)


iFₜ : ∀ {ty} → (f : funcs Σₜ ty) → IFuncs Σₜ ty iSₜ
iFₜ f = record { _⟨$⟩_ = ifₜ f ; cong = ifcongₜ f }

Semₜ : Algebra Σₜ
Semₜ = iSₜ ∥ iFₜ

hSemₜ : Homomorphism PropAlgₜ Semₜ
hSemₜ = ∣T∣ₕ Semₜ

{- Traductor -}
sₛ↝sₜ : sorts Σₛ → sorts Σₜ
sₛ↝sₜ = Function.id

-- p -> q ^ q -> p


tradImpl : ΣExpr Σₜ (bool ∷ [ bool ]) bool →
           ΣExpr Σₜ (bool ∷ [ bool ]) bool →
           ΣExpr Σₜ (bool ∷ [ bool ]) bool
tradImpl p q = orₜ ∣$∣ ((negₜ ∣$∣ (p ▹ ⟨⟩)) ▹ (q ▹ ⟨⟩))

tradAnd : ΣExpr Σₜ (bool ∷ [ bool ]) bool →
           ΣExpr Σₜ (bool ∷ [ bool ]) bool →
           ΣExpr Σₜ (bool ∷ [ bool ]) bool
tradAnd p q = negₜ ∣$∣ (orₜ ∣$∣ ((negₜ ∣$∣ (p ▹ ⟨⟩)) ▹ ((negₜ ∣$∣ (q ▹ ⟨⟩)) ▹ ⟨⟩)) ▹ ⟨⟩)

deMorgan : ∀ b b' → b ∧ b' ≡ not (not b ∨ not b')
deMorgan true true = _≡_.refl
deMorgan true false = _≡_.refl
deMorgan false true = _≡_.refl
deMorgan false false = _≡_.refl

fₛ↝fₜ : ∀ {ar} {s} → (f : funcs Σₛ (ar , s)) →
                      ΣExpr Σₜ (map sₛ↝sₜ ar) (sₛ↝sₜ s)
fₛ↝fₜ (varₛ v) = varₜ v ∣$∣ ⟨⟩
fₛ↝fₜ trueₛ = negₜ ∣$∣ ((falseₜ ∣$∣ ⟨⟩) ▹ ⟨⟩)
fₛ↝fₜ falseₛ = falseₜ ∣$∣ ⟨⟩
fₛ↝fₜ impl  = tradImpl (# zero) (# (suc zero))
fₛ↝fₜ equiv = tradAnd (tradImpl (# zero) (# (suc zero)))
                      (tradImpl (# (suc zero)) (# zero))
fₛ↝fₜ andₛ = tradAnd (# zero) (# (suc zero))
fₛ↝fₜ orₛ = orₜ ∣$∣ ((# zero) ▹ ((# (suc zero)) ▹ ⟨⟩))
fₛ↝fₜ negₛ = negₜ ∣$∣ ((# zero) ▹ ⟨⟩)

ΣₛtoΣₜ : Σₛ ↝ Σₜ
ΣₛtoΣₜ = record { ↝ₛ = sₛ↝sₜ
               ; ↝f = fₛ↝fₜ
               }


hTrad : Homomorphism PropAlgₛ (ΣₛtoΣₜ 〈 PropAlgₜ 〉)
hTrad = ∣T∣ₕ (ΣₛtoΣₜ 〈 PropAlgₜ 〉)

Enc→ : Semₛ ⟿ (ΣₛtoΣₜ 〈 Semₜ 〉)
Enc→ bool = record { _⟨$⟩_ = Function.id
                        ; cong = λ eq σ → eq σ }

condEnc→ : ∀ {ty} (f : funcs Σₛ ty) →
                   homCond Semₛ (ΣₛtoΣₜ 〈 Semₜ 〉) Enc→ f
condEnc→ (varₛ v) ⟨⟩ = λ x → PropEq.refl
condEnc→ trueₛ ⟨⟩ = λ x → PropEq.refl
condEnc→ falseₛ ⟨⟩ = λ x → PropEq.refl
condEnc→ impl (v ▹ v₁ ▹ ⟨⟩) = λ σ → PropEq.refl
condEnc→ equiv (v ▹ v₁ ▹ ⟨⟩) = λ x → deMorgan (not (v x) ∨ v₁ x) (not (v₁ x) ∨ v x)
condEnc→ andₛ (v ▹ v₁ ▹ ⟨⟩) x = deMorgan (v x) (v₁ x)
condEnc→ orₛ (v ▹ v₁ ▹ ⟨⟩) = λ _ → PropEq.refl
condEnc→ negₛ (v ▹ ⟨⟩) = λ x → PropEq.refl

Enc : Homomorphism Semₛ (ΣₛtoΣₜ 〈 Semₜ 〉)
Enc = record { ′_′ = Enc→
             ; cond = condEnc→ }


{- Extracción de la prueba de corrección -}

Exprₛ : Set
Exprₛ = Carrier (PropAlgₛ ⟦ bool ⟧ₛ)

Exprₜ : Set
Exprₜ = Carrier (ΣₛtoΣₜ 〈 PropAlgₜ 〉 ⟦ bool ⟧ₛ)

open Homomorphism

⟦_⟧ₛ_ : Exprₛ → State → Bool
⟦_⟧ₛ_ e σ = (′ hSemₛ ′ bool ⟨$⟩ e) σ

⟦_⟧ₜ_ : Exprₜ → State → Bool
⟦_⟧ₜ_ e σ = (′ hSemₜ ′ bool ⟨$⟩ e) σ

trad : Exprₛ → Exprₜ
trad e = (′ hTrad ′ bool ⟨$⟩ e)

open Initial

correct : (e : Exprₛ) → (σ : State) →
          ⟦ e ⟧ₛ σ ≡ ⟦ trad e ⟧ₜ σ
correct e = elim≈ₕ unic bool e e PropEq.refl
  where unic : (Enc ∘ₕ hSemₛ) ≈ₕ ((ΣₛtoΣₜ 〈 hSemₜ 〉ₕ) ∘ₕ hTrad)
        unic = unique (∣T∣init Σₛ) (ΣₛtoΣₜ 〈 Semₜ 〉) (Enc ∘ₕ hSemₛ)
                                 ((ΣₛtoΣₜ 〈 hSemₜ 〉ₕ) ∘ₕ hTrad)

