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
open import Data.Fin hiding (_+_ ; #_)
open import VecH

Var : Set
Var = String

{- Implementación de un compilador correcto
   utilizando el enfoque algebraico -}

-- Lenguaje de alto nivel

data Sortsₑ : Sorts where
  ExprN : Sortsₑ

data Funcsₑ : Funcs Sortsₑ where
  valN  : (n : ℕ) → Funcsₑ ([] , ExprN)
  plus  : Funcsₑ ( ExprN ∷ [ ExprN ] , ExprN )
  varN  : (v : Var) → Funcsₑ ([] , ExprN)



-- Signatura para el lenguaje

Σₑ : Signature
Σₑ = record { sorts = Sortsₑ
            ; funcs = Funcsₑ
           }


open Signature

open Setoid renaming (refl to srefl)
open Algebra


-- El lenguaje Expr es el álgebra de términos de Σₑ
ExprAlg : Algebra Σₑ
ExprAlg = ∣T∣ Σₑ



Expr : Set
Expr = Carrier (ExprAlg ⟦ ExprN ⟧ₛ)


{- Smart constructors -}
∣_∣ : ℕ → Expr
∣ n ∣ = term (valN n) ⟨⟩

_⊕_ : Expr → Expr → Expr
e₁ ⊕ e₂ = term plus (e₁ ▹ (e₂ ▹ ⟨⟩))

varₑ : Var → Expr
varₑ v = term (varN v) ⟨⟩


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

iSortsₑ : ISorts Σₑ
iSortsₑ ExprN = State →-setoid ℕ


if : ∀ {ar} {s} → (f : funcs Σₑ (ar , s)) → VecH Sortsₑ (Carrier ∘ iSortsₑ) ar →
                   Carrier (iSortsₑ s)
if (valN n) ⟨⟩ = λ σ → n
if plus (v₀ ▹ v₁ ▹ ⟨⟩) σ = v₀ σ + v₁ σ
if (varN x) ⟨⟩ = λ σ → σ x

ifcong : ∀ {ar} {s} → (f : funcs Σₑ (ar , s)) →
           {vs₀ vs₁ : VecH Sortsₑ (Carrier ∘ iSortsₑ) ar} →
           _∼v_ {R = _≈_ ∘ iSortsₑ} vs₀ vs₁ →
           _≈_ (iSortsₑ s) (if f vs₀) (if f vs₁)
ifcong (valN n) {⟨⟩} ∼⟨⟩ = λ σ → refl
ifcong plus {v₀ ▹ v₀' ▹ ⟨⟩} {v₁ ▹ v₁' ▹ ⟨⟩} (∼▹ v₀≈v₁ (∼▹ v₀'≈v₁' ∼⟨⟩)) =
                           λ σ → cong₂ _+_ (v₀≈v₁ σ) (v₀'≈v₁' σ)
ifcong (varN v) {⟨⟩} ∼⟨⟩ = λ σ → refl

iFuncsₑ : ∀ {ty} → (f : funcs Σₑ ty) → IFuncs Σₑ ty iSortsₑ
iFuncsₑ f = record { _⟨$⟩_ = if f
                   ; cong = ifcong f }

Semₑ : Algebra Σₑ
Semₑ = iSortsₑ ∥ iFuncsₑ


-- Semántica de las expresiones

open Homomorphism
open Initial

homSem : Homomorphism ExprAlg Semₑ
homSem = ∣T∣ₕ Semₑ


⟦_⟧_ : Expr → State → ℕ
⟦ e ⟧ σ = (′ homSem ′ ExprN ⟨$⟩ e) σ


-- Lenguaje de bajo nivel

data Sortsₘ : Sorts where
  Codeₛ : Sortsₘ

data Funcsₘ : Funcs Sortsₘ where
  pushₘ : (n : ℕ) → Funcsₘ ([] , Codeₛ)
  loadₘ : (v : Var) → Funcsₘ ([] , Codeₛ)
  addₘ  : Funcsₘ ([] , Codeₛ)
  seqₘ   : Funcsₘ (Codeₛ ∷ Codeₛ ∷ [] , Codeₛ)




Σₘ : Signature
Σₘ = record { sorts = Sortsₘ
            ; funcs = Funcsₘ
            }



-- El código es el álgebra de términos de Σₘ
CodeAlg : Algebra Σₘ
CodeAlg = ∣T∣ Σₘ
  

-- Semántica del lenguaje de bajo nivel



data Stack : Set where
  ε   : Stack
  _▸_ : ℕ → Stack → Stack

infixr 5 _▸_

Conf : Set
Conf = Stack × State


iSortsₘ : ISorts Σₘ
iSortsₘ Codeₛ = Conf →-setoid Maybe Stack

open import Category.Monad
open import Category.Monad.Indexed
open RawMonad {lzero} Data.Maybe.monad



ifₘ : ∀ {ar} {s} → (f : funcs Σₘ (ar , s)) → VecH Sortsₘ (Carrier ∘ iSortsₘ) ar →
                   Carrier (iSortsₘ s)
ifₘ (pushₘ n) ⟨⟩ = λ {(s , σ) → just (n ▸ s) }
ifₘ (loadₘ v) ⟨⟩ = λ {(s , σ) → just (σ v ▸ s)}
ifₘ addₘ ⟨⟩ = λ { (n₀ ▸ n₁ ▸ s , σ) → just (n₀ + n₁ ▸ s) ;
                 (_ , σ) → nothing
               }
ifₘ seqₘ (v₀ ▹ v₁ ▹ ⟨⟩) = λ {(s , σ) → v₀ (s , σ) >>= λ s' → v₁ (s' , σ)}

ifcongₘ : ∀ {ar} {s} → (f : funcs Σₘ (ar , s)) →
           {vs₀ vs₁ : VecH Sortsₘ (Carrier ∘ iSortsₘ) ar} →
           _∼v_ {R = _≈_ ∘ iSortsₘ} vs₀ vs₁ →
           _≈_ (iSortsₘ s) (ifₘ f vs₀) (ifₘ f vs₁)
ifcongₘ (pushₘ n) {⟨⟩} ∼⟨⟩ = λ _ → refl
ifcongₘ (loadₘ v) {⟨⟩} ∼⟨⟩ = λ _ → refl 
ifcongₘ addₘ {⟨⟩} ∼⟨⟩ = λ _ → refl
ifcongₘ seqₘ {v₀ ▹ v₁ ▹ ⟨⟩} {v₀' ▹ v₁' ▹ ⟨⟩} (∼▹ v₀≈v₀' (∼▹ v₁≈v₁' ∼⟨⟩)) (s , σ) =
             PropEq.trans (cong (λ ms → ms >>= λ s' → v₁ (s' , σ)) (v₀≈v₀' (s , σ)))
                          (ifcseq' (v₀' (s , σ)))
  where ifcseq' : (ms : Maybe Stack) → (ms >>= λ s' → v₁ (s' , σ))
                                        ≡ (ms >>= λ s' → v₁' (s' , σ))
        ifcseq' (just s') = v₁≈v₁' (s' , σ)
        ifcseq' nothing = refl


iFuncsₘ : ∀ {ty} → (f : funcs Σₘ ty) → IFuncs Σₘ ty iSortsₘ
iFuncsₘ f = record { _⟨$⟩_ = ifₘ f
                   ; cong = ifcongₘ f }

Exec : Algebra Σₘ
Exec = iSortsₘ ∥ iFuncsₘ


-- Como CodeAlg es el álgebra inicial, tengo homomorfismo hacia Exec
hexec : Homomorphism CodeAlg Exec
hexec = ∣T∣ₕ Exec


{- Para definir el compilador vamos a ver al código de bajo nivel
   como un álgebra de la signatura Σₑ. Para ello definimos
   un transformador de álgebras. -}



open _↝_



sₑ↝sₘ : sorts Σₑ → sorts Σₘ
sₑ↝sₘ ExprN = Codeₛ

fₑ↝fₘ : ∀ {ar} {s} → (f : funcs Σₑ (ar , s)) →
                      ΣExpr Σₘ (map sₑ↝sₘ ar) (sₑ↝sₘ s)
fₑ↝fₘ (valN n) = pushₘ n ∣$∣ ⟨⟩
fₑ↝fₘ plus     = seqₘ ∣$∣ (# (suc zero) ▹ (seqₘ ∣$∣ ((# zero) ▹ (addₘ ∣$∣ ⟨⟩) ▹ ⟨⟩)) ▹ ⟨⟩)
fₑ↝fₘ (varN v) = loadₘ v ∣$∣ ⟨⟩


ΣₑtoΣₘ : Σₑ ↝ Σₘ
ΣₑtoΣₘ = record { ↝ₛ = sₑ↝sₘ
                ; ↝f = fₑ↝fₘ
                }


{- Definamos entonces al código de bajo nivel como un álgebra de Σₑ -}

-- Código de bajo nivel como álgebra de Sigₑ
CodeAlgₑ : Algebra Σₑ
CodeAlgₑ = ΣₑtoΣₘ 〈 CodeAlg 〉

-- Semántica de bajo nivel como álgebra de Σₑ
Execₑ : Algebra Σₑ
Execₑ = ΣₑtoΣₘ 〈 Exec 〉


-- El código compilado es el carrier del sort ExprN:
Code : Set
Code = Carrier (CodeAlgₑ ⟦ ExprN ⟧ₛ)


-- Smart constructors para Code
push : ℕ → Code
push n = term (pushₘ n) ⟨⟩ 

add : Code
add = term addₘ ⟨⟩


_∙_ : Code → Code → Code
c₀ ∙ c₁ = term seqₘ (c₀ ▹ (c₁ ▹ ⟨⟩))


load : Var → Code
load v = term (loadₘ v) ⟨⟩


-- El compilador está definido por inicialidad:
homc : Homomorphism ExprAlg CodeAlgₑ
homc = ∣T∣ₕ CodeAlgₑ


compₑ : Expr → Code
compₑ e = ′ homc ′ ExprN ⟨$⟩ e 



{-
La corrección la tenemos si podemos dar un homomorfismo
entre Sem y Exec.
-}

Sem→Execₑ : Semₑ ⟿ Execₑ
Sem→Execₑ ExprN = record { _⟨$⟩_ = λ {fₑ (s , σ) → just (fₑ σ ▸ s)}
                         ; cong = λ { {f₀} {f₁} f₀≈f₁ (s , σ) →
                                      cong (λ n → just (n ▸ s)) (f₀≈f₁ σ) }
                         }


condhₛₑₘ : ∀ {ty} (f : funcs Σₑ ty) →
                       homCond Semₑ Execₑ Sem→Execₑ f
condhₛₑₘ (valN n) ⟨⟩ = λ _ → refl
condhₛₑₘ plus (f₀ ▹ f₁ ▹ ⟨⟩) = λ _ → refl
condhₛₑₘ (varN v) ⟨⟩ = λ _ → refl

hₛₑₘ : Homomorphism Semₑ Execₑ
hₛₑₘ = record { ′_′ = Sem→Execₑ
             ; cond = condhₛₑₘ }



-- Tengo también un homomorfismo entre Codeₑ y Execₑ
hexecₑ : Homomorphism CodeAlgₑ Execₑ
hexecₑ = ΣₑtoΣₘ 〈 hexec 〉ₕ


-- Función de ejecución:
⟪_⟫ : Code → Conf → Maybe Stack
⟪ c ⟫ = ′ hexecₑ ′ ExprN ⟨$⟩ c


-- Corrección del compilador: trivial por inicialidad y
-- definición de hₛₑₘ
correct : ∀ (e : Expr) → (s : Stack) → (σ : State) → 
            ⟪ compₑ e ⟫ (s , σ) ≡ just ((⟦ e ⟧ σ) ▸ s)
correct e s σ = (elim≈ₕ unic ExprN e e refl) (s , σ)
  where unic : (hexecₑ ∘ₕ homc) ≈ₕ (hₛₑₘ ∘ₕ homSem)
        unic = unique (∣T∣init Σₑ) Execₑ (hexecₑ ∘ₕ homc) (hₛₑₘ ∘ₕ homSem)

