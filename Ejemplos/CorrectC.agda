module Ejemplos.CorrectC where

open import UnivAlgebra
open import Relation.Binary
open import Data.Product
open import Data.Nat
open import Data.Bool
open import Level renaming (suc to lsuc ; zero to lzero)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open import Data.String hiding (setoid)
open import Function
open import Function.Equality renaming (_∘_ to _∘ₛ_) hiding (setoid;cong)
open import Data.List
open import Data.Maybe hiding (setoid)

Var : Set
Var = String


-- Lenguaje de alto nivel

data Sortsₑ : Set where
  NatS  : Sortsₑ
  ExprN : Sortsₑ
  Vars  : Sortsₑ

data Funcsₑ :  List Sortsₑ × Sortsₑ → Set where
  nat   : (n : ℕ) → Funcsₑ ([] , NatS)
  var   : (v : Var) → Funcsₑ ([] , Vars)
  valN  : Funcsₑ ([ NatS ] , ExprN)
  plus  : Funcsₑ ( ExprN ∷ [ ExprN ] , ExprN )
  varℕ   : Funcsₑ ([ Vars ] , ExprN)

-- Signatura para el lenguaje

Sigₑ : Signature
Sigₑ = record { sorts = Sortsₑ
             ; funcs = Funcsₑ
             }


open Signature

open Setoid renaming (refl to srefl)
open Algebra

ExprAlg : Algebra {lzero} {lzero} Sigₑ
ExprAlg = termAlgebra Sigₑ

Expr : Set
Expr = Carrier ((isorts ExprAlg) ExprN)

∣_∣ : ℕ → Expr
∣ n ∣ = term valN (term (nat n) ⟨⟩ ▹ ⟨⟩)
_⊕_ : Expr → Expr → Expr
e₁ ⊕ e₂ = term plus (e₁ ▹ (e₂ ▹ ⟨⟩))

varₑ : Var → Expr
varₑ v = term varℕ ((term (var v) ⟨⟩) ▹ ⟨⟩)

-- Ejemplo de expresión
3+3 : Expr
3+3 = ∣ 3 ∣ ⊕ ∣ 3 ∣



-- Semántica del lenguaje como álgebra
State : Set
State = Var → ℕ

emptyS : State
emptyS = λ x → 0

-- Modificación del estado
_[_←_] : State → Var → ℕ → State
σ [ x ← n ] = λ y → if y == x then n
                              else σ y



semInterpSorts : Sortsₑ → Setoid _ _
semInterpSorts NatS = setoid ℕ
semInterpSorts ExprN = State →-setoid ℕ
semInterpSorts Vars = setoid Var


semInterpFuncs : (ty : SType Sigₑ) → (f : funcs Sigₑ ty) → 
                 IFun Sigₑ ty (Carrier ∘ semInterpSorts)
semInterpFuncs ([] , .NatS) (nat n) _ = n
semInterpFuncs ([] , .Vars) (var v) _ = v
semInterpFuncs (NatS ∷ [] , ExprN) valN (x ▹ ⟨⟩) σ = x
semInterpFuncs (ExprN ∷ ExprN ∷ [] , ExprN) plus (e₁ ▹ (e₂ ▹ ⟨⟩)) σ = e₁ σ + e₂ σ
semInterpFuncs (Vars ∷ [] , ExprN) varℕ (v ▹ ⟨⟩) σ = σ v


congSemInt : ∀ {ar s f} → (ts₁ ts₂ : VecH Sigₑ (Carrier ∘ semInterpSorts) ar) →
               _≈v_ {R = _≈_ ∘ semInterpSorts} ts₁ ts₂ →
               _≈_ (semInterpSorts s) (semInterpFuncs (ar , s) f ts₁)
                              (semInterpFuncs (ar , s) f ts₂)
congSemInt {f = nat n} .⟨⟩ .⟨⟩ ≈⟨⟩ = refl
congSemInt {f = var v} .⟨⟩ .⟨⟩ ≈⟨⟩ = refl
congSemInt {f = valN} ._ ._ (≈▹ refl ≈⟨⟩) σ = refl
congSemInt {f = plus} ._ ._ (≈▹ eq (≈▹ eq' ≈⟨⟩)) σ = cong₂ (λ m n → m + n) (eq σ) (eq' σ)
congSemInt {f = varℕ} ._ ._ (≈▹ eq ≈⟨⟩) σ = cong σ eq


Sem : Algebra Sigₑ
Sem = record { isorts = semInterpSorts
             ; ifuns = semInterpFuncs
             ; ifuncong = λ {ar} {s} → congSemInt {ar} {s}
             }

-- Semántica de las expresiones

open Homomorphism
open Initial

homSem : Homomorphism Sigₑ ExprAlg Sem
homSem = tAlgHomo Sem

⟦_⟧_ : Expr → State → ℕ
⟦ e ⟧ σ = (_⟨$⟩_ (morph homSem ExprN) e) σ

-- Lenguaje de bajo nivel

data Sortsₘ : Set where
  Codeₛ : Sortsₘ
  Natₛ  : Sortsₘ
  Varsₛ : Sortsₘ

data Funcsₘ : List Sortsₘ ×  Sortsₘ → Set where
  natₘ   : (n : ℕ) → Funcsₘ ([] , Natₛ)
  varₘ   : (v : Var) → Funcsₘ ([] , Varsₛ)
  pushₘ  : Funcsₘ (Natₛ ∷ [] , Codeₛ)
  addₘ   : Funcsₘ ([] , Codeₛ)
  seqₘ   : Funcsₘ (Codeₛ ∷ Codeₛ ∷ [] , Codeₛ)
  loadₘ  : Funcsₘ (Varsₛ ∷ [] , Codeₛ)
  

Sigₘ : Signature
Sigₘ = record { sorts = Sortsₘ
              ; funcs = Funcsₘ
              }


CodeAlg : Algebra {lzero} {lzero} Sigₘ
CodeAlg = termAlgebra Sigₘ

Code : Set
Code = Carrier ((isorts CodeAlg) Codeₛ)


-- Smart constructors para Code
push : ℕ → Code
push n = term pushₘ ((term (natₘ n) ⟨⟩) ▹ ⟨⟩)

add : Code
add = term addₘ ⟨⟩

_∙_ : Code → Code → Code
c₀ ∙ c₁ = term seqₘ (c₀ ▹ (c₁ ▹ ⟨⟩))

load : Var → Code
load v = term loadₘ ((term (varₘ v) ⟨⟩) ▹ ⟨⟩)


-- Semántica del lenguaje de bajo nivel

data Stack : Set where
  ε   : Stack
  _▹_ : ℕ → Stack → Stack

infixr 5 _▹_

Conf : Set
Conf = Stack × State

execInterpSorts : Sortsₘ → Setoid _ _
execInterpSorts Codeₛ = Conf →-setoid Maybe Conf
execInterpSorts Natₛ = setoid ℕ
execInterpSorts Varsₛ = setoid Var


_>>=_ : ∀ {a b : Set} → Maybe a → (a → Maybe b) → Maybe b
(just a) >>= f = f a
nothing >>= _  = nothing


execInterpFuncs : (ty : SType Sigₘ) → (f : funcs Sigₘ ty) → 
                  IFun Sigₘ ty (Carrier ∘ execInterpSorts)
execInterpFuncs ._ (natₘ n) ⟨⟩ = n
execInterpFuncs ._ (varₘ v) ⟨⟩ = v
execInterpFuncs ._ pushₘ (n ▹ ⟨⟩) (s , σ) = just (n ▹ s , σ)
execInterpFuncs ._ addₘ ⟨⟩ (m ▹ (n ▹ s) , σ) = just ((m + n) ▹ s , σ)
execInterpFuncs ._ addₘ ⟨⟩ _ = nothing
execInterpFuncs ._ seqₘ (c₀ ▹ (c₁ ▹ ⟨⟩)) s = c₀ s >>= c₁
execInterpFuncs ._ loadₘ (v ▹ ⟨⟩) (s , σ) = just ((σ v ▹ s) , σ)


Exec : Algebra Sigₘ
Exec = record {
               isorts = execInterpSorts
             ; ifuns = execInterpFuncs
             ; ifuncong = {!!} --λ {ar} {s} → congSemInt {ar} {s}
             }

-- Ahora deberíamos poder expresar al código como un álgebra de Sigₑ
-- Definamos una función que vaya de un álgebra de Sigₑ en un álgebra
-- de Sigₘ


MtoEsorts : ∀ {l₀} {l₁} → Algebra {l₀} {l₁} Sigₘ → (s : sorts Sigₑ) → Setoid l₀ l₁
MtoEsorts a NatS = isorts a Natₛ
MtoEsorts a ExprN = isorts a Codeₛ
MtoEsorts a Vars = isorts a Varsₛ

MtoEfuncs : ∀ {l₀} {l₁} → (a : Algebra {l₀} {l₁} Sigₘ) →
            (ty : SType Sigₑ) → (f : funcs Sigₑ ty) →
            IFun {l₀} Sigₑ ty (Carrier ∘ (MtoEsorts a))
MtoEfuncs a ._ (nat n) ⟨⟩ = ifuns a ([] , Natₛ) (natₘ n) ⟨⟩
MtoEfuncs a ._ (var v) ⟨⟩ = ifuns a ([] , Varsₛ) (varₘ v) ⟨⟩
MtoEfuncs a ._ valN (n ▹ ⟨⟩) = ifuns a (Natₛ ∷ [] , Codeₛ) pushₘ (n ▹ ⟨⟩)
MtoEfuncs a ._ plus (c₀ ▹ (c₁ ▹ ⟨⟩)) =
          ifuns a (Codeₛ ∷ Codeₛ ∷ [] , Codeₛ) seqₘ
                  (c₀ ▹ (ifuns a ((Codeₛ ∷ Codeₛ ∷ []) , Codeₛ) seqₘ
                    (c₁ ▹ ((ifuns a ([] , Codeₛ) addₘ ⟨⟩) ▹ ⟨⟩)) ▹ ⟨⟩))
MtoEfuncs a .(Vars ∷ [] , ExprN) varℕ (v ▹ ⟨⟩) =
          ifuns a ((Varsₛ ∷ []) , Codeₛ) loadₘ (v ▹ ⟨⟩)

MtoE : ∀ {l₀} {l₁} → Algebra {l₀} {l₁} Sigₘ → Algebra {l₀} {l₁} Sigₑ
MtoE a = record { isorts = MtoEsorts a
                ; ifuns = MtoEfuncs a
                ; ifuncong = {!!} }

-- Código de bajo nivel como álgebra de Sigₑ
CodeAlgₑ : Algebra Sigₑ
CodeAlgₑ = MtoE CodeAlg

-- Semántica de bajo nivel como álgebra de Sigₑ
Execₑ : Algebra Sigₑ
Execₑ = MtoE Exec

-- Homomorfismo del álgebra Sem en Execₑ

m : FunAlg Sem Execₑ
m NatS = record { _⟨$⟩_ = ?
                ; cong = {!!} }
m ExprN = {!!}
m Vars = {!!}

hₛₑₘ : Homomorphism Sigₑ Sem Execₑ
hₛₑₘ = record { morph = {!!}
              ; preserv = {!!} }
