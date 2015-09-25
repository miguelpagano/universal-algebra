module Ejemplos.CorrectCompiler where

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

Var : Set
Var = String


data Sorts : Set where
  NatS  : Sorts
  ExprN : Sorts
  Vars  : Sorts

data Funcs :  List Sorts × Sorts → Set where
  nat   : (n : ℕ) → Funcs ([] , NatS)
  var   : (v : Var) → Funcs ([] , Vars)
  valN  : Funcs ([ NatS ] , ExprN)
  plus  : Funcs ( ExprN ∷ [ ExprN ] , ExprN )
  varℕ   : Funcs ([ Vars ] , ExprN)


-- Signatura para el lenguaje

Sig : Signature
Sig = record { sorts = Sorts
             ; funcs = Funcs
             }


-- Semántica del lenguaje como álgebra
State : Set
State = Var → ℕ

emptyS : State
emptyS = λ x → 0

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
semInterpFuncs ([] , .NatS) (nat n) _ = n
semInterpFuncs ([] , .Vars) (var v) _ = v
semInterpFuncs (NatS ∷ [] , ExprN) valN (x ▹ ⟨⟩) σ = x
semInterpFuncs (ExprN ∷ ExprN ∷ [] , ExprN) plus (e₁ ▹ (e₂ ▹ ⟨⟩)) σ = e₁ σ + e₂ σ
semInterpFuncs (Vars ∷ [] , ExprN) varℕ (v ▹ ⟨⟩) σ = σ v


congSemInt : ∀ {ar s f} → (ts₁ ts₂ : VecH Sig (Carrier ∘ semInterpSorts) ar) →
               _≈v_ {R = _≈_ ∘ semInterpSorts} ts₁ ts₂ →
               _≈_ (semInterpSorts s) (semInterpFuncs (ar , s) f ts₁)
                              (semInterpFuncs (ar , s) f ts₂)
congSemInt {f = nat n} .⟨⟩ .⟨⟩ ≈⟨⟩ = refl
congSemInt {f = var v} .⟨⟩ .⟨⟩ ≈⟨⟩ = refl
congSemInt {f = valN} ._ ._ (≈▹ refl ≈⟨⟩) σ = refl
congSemInt {f = plus} ._ ._ (≈▹ eq (≈▹ eq' ≈⟨⟩)) σ = cong₂ (λ m n → m + n) (eq σ) (eq' σ)
congSemInt {f = varℕ} ._ ._ (≈▹ eq ≈⟨⟩) σ = cong (λ v → σ v) eq


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

infixr 5 _▹_
infixr 4 _,_

head : ∀ {t} {st} → Stack (t ∷ st) → Val t
head (t ▹ s) = t

tail : ∀ {t} {st} → Stack (t ∷ st) → Stack st
tail (t ▹ s) = s

Conf : StackType → Set
Conf st = Stack st × State

headConf : ∀ {t} {st} → Conf (t ∷ st) → Val t
headConf = head ∘ proj₁

tailConf : ∀ {t} {st} → Conf (t ∷ st) → Conf st
tailConf (s , σ) = (tail s , σ)

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

faddm : ∀ {st} → (m : ℕ) → Stack (nat ∷ st) → Stack (nat ∷ st)
faddm m (m' ▹ s) = (m + m') ▹ s

fadd : ∀ {st} → Conf (nat ∷ nat ∷ st) → Conf (nat ∷ st)
fadd (m ▹ (n ▹ s') , σ') = (m + n) ▹ s' , σ'

add' : (c c' : Carrier (execInterpSorts ExprN)) → (st : StackType) → (Conf st) → Conf (nat ∷ st)
add' x y st (s , σ) = fadd {st} ((y ⟨$⟩ (nat ∷ st)) ((x ⟨$⟩ st) (s , σ)))

addprop : (c c' : Carrier (execInterpSorts ExprN)) → (st : StackType) → (sσ : Conf st) →
        head (proj₁ (add' c c' st sσ)) ≡ head (proj₁ ((c ⟨$⟩ st) sσ)) + head (proj₁ ((c' ⟨$⟩ st) sσ))
addprop c c' st sσ = {! rhs!}
  where sσ' : Conf []
        sσ' = (ε , emptyS)


badBad : Carrier (execInterpSorts ExprN)
badBad = record { _⟨$⟩_ = fun
                ; cong = cong'
                }
  where fun : (st : StackType) → (sσ : Conf st) → Conf (nat ∷ st)
        fun (nat ∷ st) (3 ▹ s , σ) = 8 ▹ (3 ▹ s) , σ
        fun (nat ∷ st) (x ▹ s , σ) = 10 ▹ (3 ▹ s) , σ
        fun st (s , σ) = 9 ▹ s , σ
        cong' : {i j : List Type} → i ≡ j → relIx (fun i) (fun j)
        cong' {i} refl = ext i (fun i) (fun i) (λ sσ → refl )

-- No hay forma que podamos probar que el homomorfismo respeta las
-- operaciones. El contra-ejemplo que podemos construir se basa en que
-- las funciones pueden inspeccionar los argumentos, tal como se
-- evidencia en badBad.

addIsNotFine : ∀ σ → ∃₂ (λ c c' → ¬ 
        (head (proj₁ (add' c c' [] (ε , σ))) ≡ head (proj₁ ((c ⟨$⟩ []) (ε , σ))) + head (proj₁ ((c' ⟨$⟩ []) (ε , σ)))))
addIsNotFine σ = badBad , (badBad , (λ ()))
  where
        lhs : _
        lhs = add' badBad badBad [] (ε , emptyS)
        rhs : _
        rhs = head (proj₁ ((badBad ⟨$⟩ []) (ε , σ))) + head (proj₁ ((badBad ⟨$⟩ []) (ε , σ)))


cong-add' : {st : StackType} → (t t' r r' : Carrier (execInterpSorts ExprN))
                → (eq : _≈_ (execInterpSorts ExprN) t t')
                → (eq : _≈_ (execInterpSorts ExprN) r r')
                → relIx {st} {st} (add' t r st) (add' t' r' st)
cong-add' {st} t t' r r' eq eq' =
          ext st (add' t r st)
                 (add' t' r' st)
                 (λ sσ → cong fadd (equ2 sσ))
  where prop1 : (sσ : Conf st) → (t ⟨$⟩ st) sσ ≡ (t' ⟨$⟩ st) sσ
        prop1 sσ = elimExt (t ⟨$⟩ st) (t' ⟨$⟩ st) (eq {st} {st} refl) sσ
        prop2 : (sσ sσ' : Conf (nat ∷ st)) → sσ ≡ sσ' → (r ⟨$⟩ (nat ∷ st)) sσ ≡ (r' ⟨$⟩ (nat ∷ st)) sσ'
        prop2 sσ .sσ refl = elimExt (r ⟨$⟩ nat ∷ st) (r' ⟨$⟩ nat ∷ st) (eq' {nat ∷ st} {nat ∷ st} refl) sσ
        equ2 : ∀ sσ → ( ((r ⟨$⟩ (nat ∷ st)) ((t ⟨$⟩ st) sσ)) ≡ ((r' ⟨$⟩ (nat ∷ st)) ((t' ⟨$⟩ st) sσ)))
        equ2 sσ = prop2 ((t ⟨$⟩ st) sσ) ((t' ⟨$⟩ st) sσ) (prop1 sσ)


execInterpFuncs : (ty : SType Sig) → (f : funcs Sig ty) → IFun Sig ty (Carrier ∘ execInterpSorts)
execInterpFuncs .([] , NatS) (nat n) _ = n
execInterpFuncs .([] , Vars) (var v) _ = v
execInterpFuncs .(NatS ∷ [] , ExprN) valN (x ▹ ⟨⟩) = record { _⟨$⟩_ = λ _ sσ → x ▹ proj₁ sσ , proj₂ sσ
                                                            ; cong = λ eq → extRefl eq (λ st' sσ → x ▹ proj₁ sσ , proj₂ sσ)
                                                            }
execInterpFuncs .(ExprN ∷ ExprN ∷ [] , ExprN) plus (x ▹ (y ▹ ⟨⟩)) = record { _⟨$⟩_ = add' x y
                                                                           ; cong = λ eq → extRefl eq (add' x y)
                                                                           }
                                                              
execInterpFuncs .(Vars ∷ [] , ExprN) varℕ (x ▹ ⟨⟩) = record { _⟨$⟩_ = λ _ sσ → proj₂ sσ x ▹ proj₁ sσ , proj₂ sσ
                                                           ; cong = λ eq → extRefl eq (λ _ sσ → proj₂ sσ x ▹ proj₁ sσ , proj₂ sσ) }


execSemInt : ∀ {ar s f} → (ts₁ ts₂ : VecH Sig (Carrier ∘ execInterpSorts) ar) →
               _≈v_ {R = _≈_ ∘ execInterpSorts} ts₁ ts₂ →
               _≈_ (execInterpSorts s) (execInterpFuncs (ar , s) f ts₁)
                                       (execInterpFuncs (ar , s) f ts₂)
execSemInt {f = nat n} v₁ v₂ eq = refl
execSemInt {f = var v} v₁ v₂ eq = refl
execSemInt {f = valN} ._ ._ (≈▹ refl ≈⟨⟩) refl = I.IsEquivalence.refl isEquiv
execSemInt {f = plus} (t ▹ (r ▹ .⟨⟩)) (t' ▹ (r' ▹ .⟨⟩)) (≈▹ x (≈▹ x₁ ≈⟨⟩)) refl = cong-add' t t' r r' x x₁
execSemInt {f = varℕ} (t ▹ ⟨⟩) (.t ▹ ⟨⟩) (≈▹ refl ≈⟨⟩) refl = I.IsEquivalence.refl isEquiv


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
pres .([] , NatS) (nat n) _ = refl
pres .([] , Vars) (var v) _ = refl
pres .(NatS ∷ [] , ExprN) valN (x ▹ ⟨⟩) σ = refl
pres .(ExprN ∷ ExprN ∷ [] , ExprN) plus (e₁ ▹ (e₂ ▹ ⟨⟩)) σ = {!!}
pres .(Vars ∷ [] , ExprN) varℕ (x ▹ ⟨⟩) σ = refl

hom : Homomorphism Sig Exec Sem
hom = record { morph = m
             ; preserv = pres
             }


-- Lenguaje como álgebra inicial

ExprAlg : Algebra {lzero} {lzero} Sig
ExprAlg = termAlgebra Sig

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

-- Semántica de las expresiones

open Homomorphism
open Initial

homSem : Homomorphism Sig ExprAlg Sem
homSem = proj₁ (init (tAlgInit Sig) Sem)

⟦_⟧_ : Expr → State → ℕ
⟦ e ⟧ σ = (_⟨$⟩_ (morph homSem ExprN) e) σ

-- Semántica de ejecución

homExec : Homomorphism Sig ExprAlg Exec
homExec = proj₁ (init (tAlgInit Sig) Exec)


⟪_⟫ : Expr → (st : StackType) → Conf st → Conf (nat ∷ st)
⟪ e ⟫ = _⟨$⟩_ (_⟨$⟩_ (morph homExec ExprN) e) 

-- Código


data ≈Code≈ : ∀ {st} {st'} → (Conf st → Conf st') → Set where
  _,_       : ∀ {st} {st₀} {st'} {f₀ : Conf st  → Conf st₀} 
                                 {f₁ : Conf st₀ → Conf st' }  → 
                (c₁ : ≈Code≈ f₀) → (c₂ : ≈Code≈ f₁)  → 
                ≈Code≈ (f₁ ∘ f₀)
  push      : ∀ {st} {t} → (v : Val t) →
              ≈Code≈ {st} {t ∷ st} (λ {(s , σ) → (v ▹ s , σ)})
  add       : ∀ {st} → 
              ≈Code≈ {nat ∷ nat ∷ st} {nat ∷ st}
                     fadd
  load      : ∀ {st} → (x : Var) → 
              ≈Code≈ {st} {nat ∷ st} (λ {(s , σ) → ((σ x ▹ s , σ))})


-- Compilador

{- A partir del homomorfismo del álgebra inicial al álgebra de la
ejecución del código podemos extraer el compilador.  -}

compₑ : ∀ {st}  →
        (e : Expr) → 
        ≈Code≈ {st} {nat ∷ st} (⟪ e ⟫ st)
compₑ (term valN (term (nat n) ⟨⟩ ▹ ⟨⟩)) = push n
compₑ (term plus (e₁ ▹ (e₂ ▹ ⟨⟩))) = compₑ e₁ , (compₑ e₂ , add)
compₑ (term varℕ (term (var v) ⟨⟩ ▹ ⟨⟩)) = load v

correct : ∀ {st} (e : Expr) → (s : Stack st) → (σ : State) → 
            ((⟦ e ⟧ σ) ▹ ε , σ) ≡ ⟪ e ⟫ [] (ε , σ)
correct e s σ = {!!}
  where unic : _
        unic = unique (tAlgInit Sig) Sem homSem (hom ∘ₕ homExec)
        prop : _
        prop = elimEqh unic (srefl (isorts (termAlgebra Sig) ExprN ) {x = e}) σ
