module Ejemplos.CorrectC where

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
open import Data.Fin hiding (_+_)

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

Σₑ : Signature
Σₑ = record { sorts = Sortsₑ
             ; funcs = Funcsₑ
             }


open Signature

open Setoid renaming (refl to srefl)
open Algebra


-- El lenguaje Expr es el álgebra de términos de Σₑ
ExprAlg : Algebra {lzero} {lzero} Σₑ
ExprAlg = termAlgebra Σₑ

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


semInterpFuncs : (ty : SType Σₑ) → (f : funcs Σₑ ty) → 
                 IFun Σₑ ty (Carrier ∘ semInterpSorts)
semInterpFuncs ([] , .NatS) (nat n) _ = n
semInterpFuncs ([] , .Vars) (var v) _ = v
semInterpFuncs (NatS ∷ [] , ExprN) valN (x ▹ ⟨⟩) σ = x
semInterpFuncs (ExprN ∷ ExprN ∷ [] , ExprN) plus (e₁ ▹ (e₂ ▹ ⟨⟩)) σ = e₁ σ + e₂ σ
semInterpFuncs (Vars ∷ [] , ExprN) varℕ (v ▹ ⟨⟩) σ = σ v


congSemInt : ∀ {ar s f} → (ts₁ ts₂ : VecH Σₑ (Carrier ∘ semInterpSorts) ar) →
               _≈v_ {R = _≈_ ∘ semInterpSorts} ts₁ ts₂ →
               _≈_ (semInterpSorts s) (semInterpFuncs (ar , s) f ts₁)
                              (semInterpFuncs (ar , s) f ts₂)
congSemInt {f = nat n} .⟨⟩ .⟨⟩ ≈⟨⟩ = refl
congSemInt {f = var v} .⟨⟩ .⟨⟩ ≈⟨⟩ = refl
congSemInt {f = valN} ._ ._ (≈▹ refl ≈⟨⟩) σ = refl
congSemInt {f = plus} ._ ._ (≈▹ eq (≈▹ eq' ≈⟨⟩)) σ = cong₂ (λ m n → m + n) (eq σ) (eq' σ)
congSemInt {f = varℕ} ._ ._ (≈▹ eq ≈⟨⟩) σ = cong σ eq


Sem : Algebra Σₑ
Sem = record { isorts = semInterpSorts
             ; ifuns = semInterpFuncs
             ; ifuncong = λ {ar} {s} → congSemInt {ar} {s}
             }

-- Semántica de las expresiones

open Homomorphism
open Initial

homSem : Homomorphism Σₑ ExprAlg Sem
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
  

Σₘ : Signature
Σₘ = record { sorts = Sortsₘ
              ; funcs = Funcsₘ
              }



-- El código es el álgebra de términos de Σₘ
CodeAlg : Algebra {lzero} {lzero} Σₘ
CodeAlg = termAlgebra Σₘ
  

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


execInterpFuncs : (ty : SType Σₘ) → (f : funcs Σₘ ty) → 
                  IFun Σₘ ty (Carrier ∘ execInterpSorts)
execInterpFuncs ._ (natₘ n) ⟨⟩ = n
execInterpFuncs ._ (varₘ v) ⟨⟩ = v
execInterpFuncs ._ pushₘ (n ▹ ⟨⟩) (s , σ) = just (n ▹ s , σ)
execInterpFuncs ._ addₘ ⟨⟩ (m ▹ (n ▹ s) , σ) = just ((n + m) ▹ s , σ)
execInterpFuncs ._ addₘ ⟨⟩ _ = nothing
execInterpFuncs ._ seqₘ (c₀ ▹ (c₁ ▹ ⟨⟩)) s = c₀ s >>= c₁
execInterpFuncs ._ loadₘ (v ▹ ⟨⟩) (s , σ) = just ((σ v ▹ s) , σ)


Exec : Algebra Σₘ
Exec = record {
               isorts = execInterpSorts
             ; ifuns = execInterpFuncs
             ; ifuncong = {!!}
             }

-- Como CodeAlg es el álgebra inicial, tengo homomorfismo hacia Exec
hexec : Homomorphism Σₘ CodeAlg Exec
hexec = tAlgHomo Exec


{- Para definir el compilador vamos a ver al código de bajo nivel
   como un álgebra de la signatura Σₑ. Para ello definimos
   un transformador de álgebras. -}

open SigTransf

sₑ⟶sₘ : sorts Σₑ → sorts Σₘ
sₑ⟶sₘ NatS  = Natₛ
sₑ⟶sₘ ExprN = Codeₛ
sₑ⟶sₘ Vars  = Varsₛ

-- La definición de la transformación de símbolos de función de Σₑ en Σₘ
-- es el compilador.
fₑ⟶fₘ : ∀ {ar} {s} → (f : funcs Σₑ (ar , s)) → SigExpr Σₘ (map sₑ⟶sₘ ar) (sₑ⟶sₘ s) 
fₑ⟶fₘ (nat n) = fapp (natₘ n) ⟨⟩
fₑ⟶fₘ (var v) = fapp (varₘ v) ⟨⟩
fₑ⟶fₘ valN = fapp pushₘ ((ident zero) ▹ ⟨⟩)
-- Pruebo definir el plus de una manera que no es la mas
-- natural, pero que de todas maneras es correcta.
fₑ⟶fₘ plus = fapp seqₘ (fapp pushₘ (fapp (natₘ 0) ⟨⟩ ▹ ⟨⟩ )  ▹
                  ((fapp seqₘ ((ident zero) ▹
                  ( (fapp seqₘ ( fapp addₘ ⟨⟩ ▹ (
                   ((fapp seqₘ ((ident (suc zero)) ▹ ((fapp addₘ ⟨⟩) ▹ ⟨⟩))))  ▹ ⟨⟩)) )   ▹ ⟨⟩ ))  ) ▹ ⟨⟩))
fₑ⟶fₘ varℕ = fapp loadₘ ((ident zero) ▹ ⟨⟩)


Σₑ⟶Σₘ : SigTransf Σₑ Σₘ
Σₑ⟶Σₘ = record { sortsT = sₑ⟶sₘ
                ; funsT = fₑ⟶fₘ }


{- Definamos entonces al código de bajo nivel como un álgebra de Σₑ -}

-- Código de bajo nivel como álgebra de Sigₑ
CodeAlgₑ : Algebra Σₑ
CodeAlgₑ = AlgTransf Σₑ⟶Σₘ CodeAlg

-- Semántica de bajo nivel como álgebra de Σₑ
Execₑ : Algebra Σₑ
Execₑ = AlgTransf Σₑ⟶Σₘ Exec

-- El código es el carrier del sort ExprN:
Code : Set
Code = Carrier ((isorts CodeAlgₑ) ExprN)

-- Smart constructors para Code
push : ℕ → Code
push n = term pushₘ ((term (natₘ n) ⟨⟩) ▹ ⟨⟩)

add : Code
add = term addₘ ⟨⟩

_∙_ : Code → Code → Code
c₀ ∙ c₁ = term seqₘ (c₀ ▹ (c₁ ▹ ⟨⟩))

load : Var → Code
load v = term loadₘ ((term (varₘ v) ⟨⟩) ▹ ⟨⟩)

-- El compilador está definido por inicialidad:
homc : Homomorphism Σₑ ExprAlg CodeAlgₑ
homc = tAlgHomo CodeAlgₑ

compₑ : Expr → Code
compₑ e = _⟨$⟩_ (morph homc ExprN) e

{-
La corrección la tenemos si podemos dar un homomorfismo
entre Sem y Exec.
-}

mSemCode : FunAlg Sem Execₑ
mSemCode NatS = Function.Equality.id
mSemCode ExprN =
  record { _⟨$⟩_ = λ {f (s , σ) → just (f σ ▹ s , σ)}
         ; cong = λ { {f₀} {f₁} f₀≡f₁ (s , σ) →
                  cong (λ n → just (n ▹ s , σ)) (f₀≡f₁ σ)} }
mSemCode Vars = Function.Equality.id

presSemCode : (ty : SType Σₑ) (f : funcs Σₑ ty) →
              homPreserv Σₑ Sem Execₑ mSemCode ty f
presSemCode ._ (nat n) ⟨⟩ = refl
presSemCode ._ (var v) ⟨⟩ = refl
presSemCode ._ valN (n ▹ ⟨⟩) _ = refl
presSemCode ._ plus (f₀ ▹ (f₁ ▹ ⟨⟩)) _ = refl
presSemCode ._ varℕ (v ▹ ⟨⟩) _ = refl

hₛₑₘ : Homomorphism Σₑ Sem Execₑ
hₛₑₘ = record { morph = mSemCode
              ; preserv = presSemCode }

-- Tengo también un homomorfismo entre Codeₑ y Execₑ
hexecₑ : Homomorphism Σₑ CodeAlgₑ Execₑ
hexecₑ = HomTransf Σₑ⟶Σₘ hexec

-- Función de ejecución:
⟪_⟫ : Code → Conf → Maybe Conf
⟪ c ⟫ = _⟨$⟩_ (morph hexecₑ ExprN) c

-- Corrección del compilador: trivial por inicialidad y
-- definición de hₛₑₘ
correct : ∀ (e : Expr) → (σ : State) → 
            ⟪ compₑ e ⟫ (ε , σ) ≡ just ((⟦ e ⟧ σ) ▹ ε , σ)
correct e σ = elim≈ₕ unic ExprN e e refl (ε , σ)
  where unic : (hexecₑ ∘ₕ homc) ≈ₕ (hₛₑₘ ∘ₕ homSem)
        unic = unique (tAlgInit Σₑ) Execₑ (hexecₑ ∘ₕ homc) (hₛₑₘ ∘ₕ homSem)


