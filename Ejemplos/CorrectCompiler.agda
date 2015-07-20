module Ejemplos.CorrectCompiler where

open import UnivAlgebra
open import Relation.Binary
open import Data.Product
open import Data.Nat
open import Data.Bool
open import Level renaming (suc to lsuc ; zero to lzero)
open import Relation.Binary.PropositionalEquality as PropEq
open import Data.String hiding (setoid)
open import Function
open import Data.List

data Sorts : Set where
  NatS  : Sorts
  BoolS : Sorts
  ExprN : Sorts
  ExprB : Sorts
  Stmt  : Sorts
  Vars  : Sorts

data Funcs : Set where
  valN  : Funcs
  valB  : Funcs
  plus  : Funcs
  var   : Funcs
  assgn : Funcs
  comp  : Funcs
  if    : Funcs
  for   : Funcs
  while : Funcs


arityFuncs : Funcs  → NProd Sorts
arityFuncs valN = 1 , NatS , ExprN
arityFuncs valB = 1 , BoolS , ExprB
arityFuncs plus = 2 , (ExprN , ExprN) , ExprN
arityFuncs var = 1 , Vars , ExprN
arityFuncs assgn = 2 , (Vars , ExprN) , Stmt
arityFuncs comp = 2 , (Stmt , Stmt) , Stmt
arityFuncs if = 3 , ((ExprB , Stmt) , Stmt) , Stmt
arityFuncs for = 2 , (ExprN , Stmt) , Stmt
arityFuncs while = 2 , (ExprB , Stmt) , Stmt

-- Signatura para el lenguaje

Sig : Signature
Sig = record { sorts = Sorts
             ; funcs = Funcs
             ; arity = arityFuncs
             }


-- Semántica del lenguaje como álgebra

Var : Set
Var = String

State : Set
State = Var → ℕ

-- Modificación del estado
_[_←_] : State → Var → ℕ → State
σ [ x ← n ] = λ y → if y == x then n
                              else σ y

semInterpSorts : Sorts → Setoid _ _
semInterpSorts NatS = setoid ℕ
semInterpSorts BoolS = setoid Bool
semInterpSorts ExprN = setoid ((σ : State) → ℕ)
semInterpSorts ExprB = setoid ((σ : State) → Bool)
semInterpSorts Stmt = setoid ((m : ℕ) → (σ : State) → State)
semInterpSorts Vars = setoid Var

open Signature

open Setoid

forRec : ℕ → (State → State) → State → State
forRec zero f σ = σ
forRec (suc n) f σ = forRec n f (f σ)

wRec : ℕ → (State → State) → (State → Bool) → State → State
wRec zero f fcond σ    = σ
wRec (suc n) f fcond σ = if (fcond σ) then wRec n f fcond (f σ)
                                      else σ


semInterpFuncs : (f : Funcs) →
                 Fun Sorts (arity Sig f) (Carrier ∘ semInterpSorts)
semInterpFuncs valN n σ = n
semInterpFuncs valB b σ = b
semInterpFuncs plus (fn₁ , fn₂) σ = fn₁ σ + fn₂ σ
semInterpFuncs var v σ = σ v
semInterpFuncs assgn (v , fn) m σ = σ [ v ← fn σ ]
semInterpFuncs comp (fst₁ , fst₂) m σ = fst₂ m (fst₁ m σ)
semInterpFuncs if ((fb , fst₁) , fst₂) m σ = if fb σ then fst₁ m σ
                                                     else fst₂ m σ
semInterpFuncs for (fn , fst) m σ = forRec (fn σ) (fst m) σ
semInterpFuncs while (fb , fst) m σ = wRec m (fst m) fb σ

Sem : Algebra Sig
Sem = record { isorts = semInterpSorts
             ; ifuns = semInterpFuncs
             }


-- Ejecución de máquina como álgebra

-- Tipos
data Type : Set where
  bool : Type
  nat  : Type

-- Valores
Val : Type → Set
Val bool = Bool
Val nat  = ℕ

StackType : Set
StackType = List Type

data Stack : (st : StackType) → Set where
  ε   : Stack []
  _▹_ : ∀ {t} {st} → Val t → Stack st → Stack (t ∷ st)

head : ∀ {t} {st} → Stack (t ∷ st) → Val t
head (t ▹ s) = t

tail : ∀ {t} {st} → Stack (t ∷ st) → Stack st
tail (t ▹ s) = s

Conf : StackType → Set
Conf st = Stack st × State

execInterpSorts : Sorts → Setoid _ _
execInterpSorts NatS = setoid ℕ
execInterpSorts BoolS = setoid Bool
execInterpSorts ExprN = setoid (∀ {st} → (sσ : Conf st) → Conf (nat ∷ st))
execInterpSorts ExprB = setoid (∀ {st} → (sσ : Conf st) → Conf (bool ∷ st))
execInterpSorts Stmt = setoid (∀ {st} → ℕ → (sσ : Conf st) → Conf st)
execInterpSorts Vars = setoid Var


execInterpFuncs : (f : Funcs) →
                  Fun Sorts (arity Sig f) (Carrier ∘ execInterpSorts)
execInterpFuncs valN n (s , σ) = n ▹ s , σ
execInterpFuncs valB b (s , σ) = (b ▹ s) , σ
execInterpFuncs plus (fn₁ , fn₂) (s , σ) = ((n₁ + n₂) ▹ s) , σ
  where n₁ : ℕ
        n₁ = head $ proj₁ (fn₁ (s , σ))
        n₂ : ℕ
        n₂ = head $ proj₁ (fn₂ (s , σ))
execInterpFuncs var v (s , σ) = (σ v ▹ s) , σ
execInterpFuncs assgn (v , fn) {st} m sσ = s' , σ' [ v ← n ]
  where s' : Stack st
        s' = tail $ proj₁ $ fn sσ
        σ' : State
        σ' = proj₂ $ fn sσ
        n  : ℕ
        n = head $ proj₁ $ fn sσ
execInterpFuncs comp (fstmt₁ , fstmt₂) m sσ = fstmt₂ m (fstmt₁ m sσ)
execInterpFuncs if x sσ = {!!}
execInterpFuncs for x sσ = {!!}
execInterpFuncs while x sσ = {!!}


Exec : Algebra Sig
Exec = record { isorts = execInterpSorts
              ; ifuns = execInterpFuncs
              }



-- Homomorfismo

m : (s : Sorts) → Carrier (execInterpSorts s) → Carrier (semInterpSorts s)
m s = {!!} 


hom : Homomorphism Sig Exec Sem
hom = record { morphs = {!!}
             ; preserv = {!!}
             }
