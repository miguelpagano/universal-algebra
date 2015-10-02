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


-- El lenguaje Expr es el álgebra de términos de Sigₑ
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



-- El código es el álgebra de términos de Sigₘ
CodeAlg : Algebra {lzero} {lzero} Sigₘ
CodeAlg = termAlgebra Sigₘ


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
execInterpFuncs ._ addₘ ⟨⟩ (m ▹ (n ▹ s) , σ) = just ((n + m) ▹ s , σ)
execInterpFuncs ._ addₘ ⟨⟩ _ = nothing
execInterpFuncs ._ seqₘ (c₀ ▹ (c₁ ▹ ⟨⟩)) s = c₀ s >>= c₁
execInterpFuncs ._ loadₘ (v ▹ ⟨⟩) (s , σ) = just ((σ v ▹ s) , σ)


Exec : Algebra Sigₘ
Exec = record {
               isorts = execInterpSorts
             ; ifuns = execInterpFuncs
             ; ifuncong = {!!}
             }

-- Como CodeAlg es el álgebra inicial, tengo homomorfismo hacia Exec
hexec : Homomorphism Sigₘ CodeAlg Exec
hexec = tAlgHomo Exec


-- Ahora deberíamos poder expresar al código como un álgebra de Sigₑ
-- Definamos una función que vaya de un álgebra de Sigₑ en un álgebra
-- de Sigₘ: Un transformador de álgebras.

MtoEsorts : sorts Sigₑ → sorts Sigₘ
MtoEsorts NatS = Natₛ
MtoEsorts ExprN = Codeₛ
MtoEsorts Vars = Varsₛ

MtoEisorts : ∀ {l₀} {l₁} → Algebra {l₀} {l₁} Sigₘ → (s : sorts Sigₑ) → Setoid l₀ l₁
MtoEisorts a s = isorts a (MtoEsorts s)

MtoEfuncs : ∀ {l₀} {l₁} → (a : Algebra {l₀} {l₁} Sigₘ) →
            (ty : SType Sigₑ) → (f : funcs Sigₑ ty) →
            IFun {l₀} Sigₑ ty (Carrier ∘ (MtoEisorts a))
MtoEfuncs a ._ (nat n) ⟨⟩ = ifuns a ([] , Natₛ) (natₘ n) ⟨⟩
MtoEfuncs a ._ (var v) ⟨⟩ = ifuns a ([] , Varsₛ) (varₘ v) ⟨⟩
MtoEfuncs a ._ valN (n ▹ ⟨⟩) = ifuns a (Natₛ ∷ [] , Codeₛ) pushₘ (n ▹ ⟨⟩)
MtoEfuncs a ._ plus (c₀ ▹ (c₁ ▹ ⟨⟩)) =
          ifuns a (Codeₛ ∷ Codeₛ ∷ [] , Codeₛ) seqₘ
                  (c₀ ▹ (ifuns a ((Codeₛ ∷ Codeₛ ∷ []) , Codeₛ) seqₘ
                    (c₁ ▹ ((ifuns a ([] , Codeₛ) addₘ ⟨⟩) ▹ ⟨⟩)) ▹ ⟨⟩))
MtoEfuncs a .(Vars ∷ [] , ExprN) varℕ (v ▹ ⟨⟩) =
          ifuns a ((Varsₛ ∷ []) , Codeₛ) loadₘ (v ▹ ⟨⟩)

MtoEAlg : ∀ {l₀} {l₁} → Algebra {l₀} {l₁} Sigₘ → Algebra {l₀} {l₁} Sigₑ
MtoEAlg a = record { isorts = MtoEisorts a
                ; ifuns = MtoEfuncs a
                ; ifuncong = {!!} }

-- Ahora quisiera ver si dado un homomorfismo en la signatura Sigₘ
-- Puedo tener uno en la signatura Sigₑ. Esto es válido por algún teorema
-- importante de teoría de categorías. Si tengo un transformador de álgebras,
-- los homomorfismos se preservan.

MtoEPreserv : ∀ {l₀} {l₁} {a₀ : Algebra {l₀} {l₁} Sigₘ} {a₁ : Algebra {l₀} {l₁} Sigₘ}
              {hₘ : Homomorphism {l₀} {l₁} Sigₘ a₀ a₁} →
              (ty : SType Sigₑ) (f : funcs Sigₑ ty) →
              homPreserv Sigₑ (MtoEAlg a₀) (MtoEAlg a₁) ((morph hₘ) ∘ MtoEsorts)
              ty f
MtoEPreserv .([] , NatS) (nat n) ⟨⟩ = {!!}
MtoEPreserv .([] , Vars) (var v) as = {!!}
MtoEPreserv .(NatS ∷ [] , ExprN) valN as = {!!}
MtoEPreserv .(ExprN ∷ ExprN ∷ [] , ExprN) plus as = {!!}
MtoEPreserv .(Vars ∷ [] , ExprN) varℕ as = {!!}

MtoEHom : ∀ {l₀} {l₁} {a₀} {a₁} →
            Homomorphism {l₀} {l₁} Sigₘ a₀ a₁ →
            Homomorphism {l₀} {l₁} Sigₑ (MtoEAlg a₀) (MtoEAlg a₁)
MtoEHom {a₀ = a₀} {a₁ = a₁} hₘ =
              record { morph = (morph hₘ) ∘ MtoEsorts
                     ; preserv = MtoEPreserv  {a₀ = a₀} {a₁ = a₁} {hₘ = hₘ}}



{- Ahora lo que hacemos es llevar el código de bajo nivel y su semántica a la signatura
   Sigₘ -}

-- Código de bajo nivel como álgebra de Sigₑ
CodeAlgₑ : Algebra Sigₑ
CodeAlgₑ = MtoEAlg CodeAlg

-- Semántica de bajo nivel como álgebra de Sigₑ
Execₑ : Algebra Sigₑ
Execₑ = MtoEAlg Exec


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
homc : Homomorphism Sigₑ ExprAlg CodeAlgₑ
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

presSemCode : (ty : SType Sigₑ) (f : funcs Sigₑ ty) →
              homPreserv Sigₑ Sem Execₑ mSemCode ty f
presSemCode ._ (nat n) ⟨⟩ = refl
presSemCode ._ (var v) ⟨⟩ = refl
presSemCode ._ valN (n ▹ ⟨⟩) _ = refl
presSemCode ._ plus (f₀ ▹ (f₁ ▹ ⟨⟩)) _ = refl
presSemCode ._ varℕ (v ▹ ⟨⟩) _ = refl

hₛₑₘ : Homomorphism Sigₑ Sem Execₑ
hₛₑₘ = record { morph = mSemCode
              ; preserv = presSemCode }

-- Tengo también un homomorfismo entre Codeₑ y Execₑ
hexecₑ : Homomorphism Sigₑ CodeAlgₑ Execₑ
hexecₑ = MtoEHom hexec

-- Función de ejecución:
⟪_⟫ : Code → Conf → Maybe Conf
⟪ c ⟫ = _⟨$⟩_ (morph hexecₑ ExprN) c


-- Corrección del compilador: trivial por inicialidad y
-- definición de hₛₑₘ
correct : ∀ (e : Expr) → (σ : State) → 
            ⟪ compₑ e ⟫ (ε , σ) ≡ just ((⟦ e ⟧ σ) ▹ ε , σ)
correct e σ = elimEqh unic refl -- Ver por qué me pinta de amarillo acá
  where unic : (hₛₑₘ ∘ₕ homSem) ≈ₕ (hexecₑ ∘ₕ homc)
        unic = unique (tAlgInit Sigₑ) Execₑ (hₛₑₘ ∘ₕ homSem) (hexecₑ ∘ₕ homc)
