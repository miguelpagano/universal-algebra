module Ejemplos.CorrectCompiler where

open import UnivAlgebra
open import Relation.Binary
open import Data.Product
open import Data.Nat
open import Data.Bool
open import Level renaming (suc to lsuc ; zero to lzero)
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open import Data.String hiding (setoid)
open import Function
open import Function.Equality renaming (_∘_ to _∘ₛ_) hiding (setoid;cong)
open import Data.List

data Sorts : Set where
  NatS  : Sorts
  ExprN : Sorts
  Vars  : Sorts

data Funcs :  List Sorts × Sorts → Set where
  valN  : Funcs ([ NatS ] , ExprN)
  plus  : Funcs ( ExprN ∷ [ ExprN ] , ExprN )
  var   : Funcs ([ Vars ] , ExprN)


-- Signatura para el lenguaje

Sig : Signature
Sig = record { sorts = Sorts
             ; funcs = Funcs
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
semInterpSorts ExprN =  (State) →-setoid ℕ
semInterpSorts Vars = setoid Var

open Signature

open Setoid renaming (refl to srefl)

forRec : ℕ → (State → State) → State → State
forRec zero f σ = σ
forRec (suc n) f σ = forRec n f (f σ)

wRec : ℕ → (State → State) → (State → Bool) → State → State
wRec zero f fcond σ    = σ
wRec (suc n) f fcond σ = if (fcond σ) then wRec n f fcond (f σ)
                                      else σ
open Algebra

semInterpFuncs : (ty : SType Sig) → (f : funcs Sig ty) → 
                 IFun Sig ty (Carrier ∘ semInterpSorts)
semInterpFuncs ([] , _) () _
semInterpFuncs (NatS ∷ [] , ExprN) valN (x ▹ ⟨⟩) σ = x
semInterpFuncs (ExprN ∷ ExprN ∷ [] , ExprN) plus (e₁ ▹ (e₂ ▹ ⟨⟩)) σ = e₁ σ + e₂ σ
semInterpFuncs (Vars ∷ [] , ExprN) var (v ▹ ⟨⟩) σ = σ v

congSemInt : ∀ {ar s f} → (ts₁ ts₂ : VecH Sig (Carrier ∘ semInterpSorts) ar) →
               _≈v_ {R = _≈_ ∘ semInterpSorts} ts₁ ts₂ →
               _≈_ (semInterpSorts s) (semInterpFuncs (ar , s) f ts₁)
                              (semInterpFuncs (ar , s) f ts₂)
congSemInt {f = valN} ._ ._ (≈▹ refl ≈⟨⟩) σ = refl
congSemInt {f = plus} ._ ._ (≈▹ eq (≈▹ eq' ≈⟨⟩)) σ = cong₂ (λ m n → m + n) (eq σ) (eq' σ)
congSemInt {f = var} ._ ._ (≈▹ eq ≈⟨⟩) σ = cong (λ v → σ v) eq


Sem : Algebra Sig
Sem = record { isorts = semInterpSorts
             ; ifuns = semInterpFuncs
             ; ifuncong = λ {ar} {s} → congSemInt {ar} {s}
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

open import Relation.Binary.Indexed as I hiding (Setoid)

data relIx : {st st' : StackType} → (f : Conf st → Conf (nat ∷ st)) → (g : Conf st' → Conf (nat ∷ st')) → Set where
    ext : (st : StackType) (f g : Conf st → Conf (nat ∷ st)) → ((sσ : Conf st) → f sσ ≡ g sσ) → relIx {st} {st} f g

isEquiv : I.IsEquivalence (λ st → Conf st → Conf (nat ∷ st))
                       (λ {st} {st'} → relIx {st} {st'})
isEquiv = record { refl = λ {i} {x} → ext i x x (λ sσ → refl)
                 ; sym = sym'
                 ; trans = trans'
                 }
        where sym' : I.Symmetric (λ st → Conf st → Conf (nat ∷ st)) relIx
              sym' (ext st f g x) = ext st g f (λ y → PropEq.sym (x y))
              trans' : I.Transitive (λ st → Conf st → Conf (nat ∷ st)) relIx
              trans' (ext st f g x) (ext .st .g h y) =
                ext st f h (λ sσ → PropEq.trans (x sσ) (y sσ))

extRefl : {st st' : List Type} → st ≡ st' → (f : (st'' : StackType) → Conf st'' → Conf (nat ∷ st'')) → relIx {st} {st'} (f st) (f st')
extRefl {st} refl f = ext st (f st) (f st) (λ sσ → refl)


execInterpSorts : Sorts → Setoid _ _
execInterpSorts NatS = setoid ℕ
execInterpSorts Vars = setoid Var
execInterpSorts ExprN = Function.Equality.setoid (setoid StackType) setIx
   where setIx : I.Setoid StackType lzero lzero
         setIx = record { Carrier = λ st → (sσ : Conf st) → Conf (nat ∷ st)
                        ; _≈_ = relIx
                        ; isEquivalence = isEquiv
                        }

elimExt : ∀ {st} f g → relIx {st} {st} f g → (sσ : Conf st) → f sσ ≡ g sσ
elimExt f g (ext st .f .g x) sσ = x sσ

add' : Carrier (execInterpSorts ExprN) → Carrier (execInterpSorts ExprN) → (st : StackType) → (Conf st) → Conf (nat ∷ st)
add' x y st s = (m + n) ▹ proj₁ s , proj₂ s
  where m : ℕ
        m = head (proj₁ ((x ⟨$⟩ st) s))
        n : ℕ
        n = head (proj₁ ((y ⟨$⟩ st) s))

cong-add' : {st : StackType} → (t t' r r' : Carrier (execInterpSorts ExprN))
                → (eq : _≈_ (execInterpSorts ExprN) t t')
                → (eq : _≈_ (execInterpSorts ExprN) r r')
                → relIx {st} {st} (add' t r st) (add' t' r' st)
cong-add' {st} t t' r r' eq eq' = ext st (add' t r st) (add' t' r' st) (λ sσ → cong₂ (λ m n → (m + n) ▹ proj₁ sσ , proj₂ sσ) (m≡m' sσ) (n≡n' sσ))
  where prop1 : (sσ : Conf st) → (t ⟨$⟩ st) sσ ≡ (t' ⟨$⟩ st) sσ
        prop1 sσ = elimExt (t ⟨$⟩ st) (t' ⟨$⟩ st) (eq {st} {st} refl) sσ
        prop2 : (sσ : Conf st) → (r ⟨$⟩ st) sσ ≡ (r' ⟨$⟩ st) sσ
        prop2 sσ = elimExt (r ⟨$⟩ st) (r' ⟨$⟩ st) (eq' {st} {st} refl) sσ
        m : Conf st → ℕ
        m sσ = head (proj₁ ((t ⟨$⟩ st) sσ))
        m' : Conf st → ℕ
        m' sσ = head (proj₁ ((t' ⟨$⟩ st) sσ))
        m≡m' : (sσ : Conf st) → m sσ ≡ m' sσ
        m≡m' sσ = cong (λ sσ' → head (proj₁ sσ')) (prop1 sσ)
        n : Conf st → ℕ
        n sσ = head (proj₁ ((r ⟨$⟩ st) sσ))
        n' : Conf st → ℕ
        n' sσ = head (proj₁ ((r' ⟨$⟩ st) sσ))
        n≡n' : (sσ : Conf st) → n sσ ≡ n' sσ
        n≡n' sσ = cong (λ sσ' → head (proj₁ sσ')) (prop2 sσ)
        
execInterpFuncs : (ty : SType Sig) → (f : funcs Sig ty) → IFun Sig ty (Carrier ∘ execInterpSorts)
execInterpFuncs .(NatS ∷ [] , ExprN) valN (x ▹ ⟨⟩) = record { _⟨$⟩_ = λ _ sσ → x ▹ proj₁ sσ , proj₂ sσ
                                                            ; cong = λ eq → extRefl eq (λ st' sσ → x ▹ proj₁ sσ , proj₂ sσ)
                                                            }
execInterpFuncs .(ExprN ∷ ExprN ∷ [] , ExprN) plus (x ▹ (y ▹ ⟨⟩)) = record { _⟨$⟩_ = add' x y
                                                                           ; cong = λ eq → extRefl eq (add' x y)
                                                                           }
                                                              
execInterpFuncs .(Vars ∷ [] , ExprN) var (x ▹ ⟨⟩) = record { _⟨$⟩_ = λ _ sσ → proj₂ sσ x ▹ proj₁ sσ , proj₂ sσ
                                                           ; cong = λ eq → extRefl eq (λ _ sσ → proj₂ sσ x ▹ proj₁ sσ , proj₂ sσ) }


execSemInt : ∀ {ar s f} → (ts₁ ts₂ : VecH Sig (Carrier ∘ execInterpSorts) ar) →
               _≈v_ {R = _≈_ ∘ execInterpSorts} ts₁ ts₂ →
               _≈_ (execInterpSorts s) (execInterpFuncs (ar , s) f ts₁)
                                       (execInterpFuncs (ar , s) f ts₂)
execSemInt {f = valN} ._ ._ (≈▹ refl ≈⟨⟩) refl = I.IsEquivalence.refl isEquiv
execSemInt {f = plus} (t ▹ (r ▹ .⟨⟩)) (t' ▹ (r' ▹ .⟨⟩)) (≈▹ x (≈▹ x₁ ≈⟨⟩)) refl = cong-add' t t' r r' x x₁
execSemInt {f = var} (t ▹ ⟨⟩) (.t ▹ ⟨⟩) (≈▹ refl ≈⟨⟩) refl = I.IsEquivalence.refl isEquiv


Exec : Algebra Sig
Exec = record { isorts = execInterpSorts
              ; ifuns = execInterpFuncs
              ; ifuncong = λ {ar} {s} {f} → execSemInt {ar} {s} {f}
              }



-- -- Homomorfismo

m : (s : Sorts) → (execInterpSorts s) ⟶ (semInterpSorts s)
m NatS = record { _⟨$⟩_ = λ x → x ; cong = λ {i} {j} z → z }
m ExprN = record { _⟨$⟩_ = λ x σ → head (proj₁ ((x ⟨$⟩ []) (ε , σ)))
                 ; cong = λ {i} {j} x σ → cong (λ sσ → head (proj₁ sσ)) (elimExt {[]} (i ⟨$⟩ []) (j ⟨$⟩ []) (x {[]} {[]} refl) (ε , σ))
                 }
m Vars = record { _⟨$⟩_ = λ x → x ; cong = λ x → x }

pres : (ty : SType Sig) (f : funcs Sig ty) → homPreserv Sig Exec Sem m ty f
pres .(NatS ∷ [] , ExprN) valN (x ▹ ⟨⟩) σ = refl
pres .(ExprN ∷ ExprN ∷ [] , ExprN) plus (x ▹ (x₁ ▹ ⟨⟩)) σ = refl
pres .(Vars ∷ [] , ExprN) var (x ▹ ⟨⟩) σ = refl

hom : Homomorphism Sig Exec Sem
hom = record { morph = m
             ; preserv = pres
             }

