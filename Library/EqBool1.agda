module EqBool1 where

open import UnivAlgebra
open import Equational
open import Data.Unit hiding (setoid)
open import Data.List
open import Data.Product
open import Data.Nat
open import Data.Sum

data Σops₁ : List ⊤ × ⊤ → Set where
  t₁   : Σops₁ ([] ↦ tt)
  f₁   : Σops₁ ([] ↦ tt)
  neg₁ : Σops₁ ([ tt ] ↦ tt)
  and₁ : Σops₁ ((tt ∷ [ tt ]) ↦ tt)
  or₁  : Σops₁ ((tt ∷ [ tt ]) ↦ tt)


Σbool₁ : Signature
Σbool₁ = ⟨ ⊤ , Σops₁ ⟩

Vars₁ : Vars Σbool₁
Vars₁ s = ℕ

Eq₁ : Set
Eq₁ = Equation Σbool₁ Vars₁ tt

open TermAlgebra
open Signature
open import HeterogenuousVec

-- A formula is a term of the Term Algebra
Form₁ : Set
Form₁ = HU (Σbool₁ 〔 Vars₁ 〕) tt

-- smart constructors
_∧₁_ : Form₁ → Form₁ → Form₁
φ ∧₁ ψ = term and₁ ⟨⟨ φ , ψ ⟩⟩

_∨₁_ : Form₁ → Form₁ → Form₁
φ ∨₁ ψ = term or₁ ⟨⟨ φ , ψ ⟩⟩

¬ : Form₁ → Form₁
¬ φ = term neg₁ ⟪ φ ⟫

p : Form₁
p = term (inj₂ 0) ⟨⟩

q : Form₁
q = term (inj₂ 1) ⟨⟩

r : Form₁
r = term (inj₂ 2) ⟨⟩

true₁ : Form₁
true₁ = term (inj₁ t₁) ⟨⟩

false₁ : Form₁
false₁ = term (inj₁ f₁) ⟨⟩

-- Axioms
assocAnd₁ : Eq₁
assocAnd₁ = ⋀ p ∧₁ (q ∧₁ r) ≈ ((p ∧₁ q) ∧₁ r)

commAnd₁ : Eq₁
commAnd₁ = ⋀ p ∧₁ q ≈ (q ∧₁ p)

assocOr₁ : Eq₁
assocOr₁ = ⋀ p ∨₁ (q ∨₁ r) ≈ ((p ∨₁ q) ∨₁ r)

commOr₁ : Eq₁
commOr₁ = ⋀ p ∨₁ q ≈ (q ∨₁ p)

idemAnd₁ : Eq₁
idemAnd₁ = ⋀ p ∧₁ p ≈ p

idemOr₁ : Eq₁
idemOr₁ = ⋀ p ∨₁ p ≈ p

distAndOr₁ : Eq₁
distAndOr₁ = ⋀ p ∧₁ (q ∨₁ r) ≈ ((p ∧₁ q) ∨₁ (p ∧₁ r))

distOrAnd₁ : Eq₁
distOrAnd₁ = ⋀ p ∨₁ (q ∧₁ r) ≈ ((p ∨₁ q) ∧₁ (p ∨₁ r))

n₁ : Eq₁
n₁ = ⋀ p ∧₁ (p ∨₁ q) ≈ p

n₂ : Eq₁
n₂ = ⋀ p ∨₁ (p ∧₁ q) ≈ p

andF : Eq₁
andF = ⋀ p ∧₁ (¬ p) ≈ false₁

orT : Eq₁
orT = ⋀ p ∨₁ (¬ p) ≈ true₁


repeat : ∀ {A : Set} → A → ℕ → List A
repeat a zero = []
repeat a (suc n) = a ∷ repeat a n


Tbool₁ : Theory Σbool₁ Vars₁ (repeat tt 12)
Tbool₁ = assocAnd₁ ▹ commAnd₁ ▹ assocOr₁ ▹
         commOr₁ ▹ idemAnd₁ ▹ idemOr₁ ▹
         distAndOr₁ ▹ distOrAnd₁ ▹ n₁ ▹
         n₂ ▹ andF ▹ orT ▹ ⟨⟩

pattern ax₁ = here
pattern ax₂ = there here
pattern ax₃ = there (there here)
pattern ax₄ = there (there (there here))
pattern ax₅ = there (there (there (there here)))
pattern ax₆ = there (there (there (there (there here))))
pattern ax₇ = there (there (there (there (there (there here)))))
pattern ax₈ = there (there (there (there (there (there (there here))))))
pattern ax₉ = there (there (there (there (there (there (there (there here)))))))
pattern ax₁₀ = there (there (there (there (there (there (there
                                                      (there (there here))))))))
pattern ax₁₁ = there (there (there (there (there (there (there (there (there
                                                            (there here)))))))))
pattern ax₁₂ = there (there (there (there (there (there (there (there (there
                                                    (there (there here))))))))))



module BoolModel₁ where

  open import Data.Bool
  open import Relation.Binary.PropositionalEquality as PE
  open import Relation.Binary
  open import Function.Equality hiding (setoid)

  BCarrier : sorts Σbool₁ → Setoid _ _
  BCarrier _ = setoid Bool

  Bops : ∀ {ar s} → (f : ops Σbool₁ (ar , s)) →
           BCarrier ✳ ar ⟶ BCarrier s
  Bops t₁ = record { _⟨$⟩_ = λ _ → true ; cong = λ _ → refl }
  Bops f₁ = record { _⟨$⟩_ = λ _ → false ; cong = λ _ → refl }
  Bops neg₁ = record { _⟨$⟩_ = λ { (b ▹ ⟨⟩) → not b }
                     ; cong = λ { {b₀ ▹ ⟨⟩} {b₁ ▹ ⟨⟩} (∼▹ b₀≡b₁ _) → PE.cong not b₀≡b₁ } }
  Bops and₁ = record { _⟨$⟩_ = λ { (b ▹ b' ▹ ⟨⟩) → b ∧ b' } ;
                       cong = λ { {b₀ ▹ b₀' ▹ ⟨⟩} {b₁ ▹ b₁' ▹ ⟨⟩} (∼▹ b₀≡b₁ (∼▹ b₀'≡b₁' ∼⟨⟩)) →
                                  cong₂ _∧_ b₀≡b₁ b₀'≡b₁' } }
  Bops or₁ = record { _⟨$⟩_ = λ { (b ▹ b' ▹ ⟨⟩) → b ∨ b' } ;
                      cong = λ { {b₀ ▹ b₀' ▹ ⟨⟩} {b₁ ▹ b₁' ▹ ⟨⟩} (∼▹ b₀≡b₁ (∼▹ b₀'≡b₁' ∼⟨⟩)) →
                                cong₂ _∨_ b₀≡b₁ b₀'≡b₁' } }


  B₁ : Algebra Σbool₁
  B₁ = BCarrier ∥ Bops

  open Equation



module Proofs₁ where
  open ProvSetoid
  open import Relation.Binary.EqReasoning (ProvSetoid Tbool₁ tt)
  open Subst {Σbool₁} {Vars₁}
  
  p₁ : Tbool₁ ⊢ (⋀ ¬ p ∧₁ p ≈ false₁)
  p₁ = begin
         ¬ p ∧₁ p
         ≈⟨ psubst ax₂ σ₁ ∼⟨⟩ ⟩
         p ∧₁ ¬ p
         ≈⟨ psubst ax₁₁ idSubst ∼⟨⟩ ⟩
         false₁
       ∎
    where σ₁ : Subst
          σ₁ 0 = ¬ p
          σ₁ 1 = p
          σ₁ n = term (inj₂ n) ⟨⟩

  p₂ : Tbool₁ ⊢ (⋀ false₁ ≈ ¬ true₁)
  p₂ = {!!}

  deM₁ : Tbool₁ ⊢ (⋀ ¬ (p ∧₁ q) ≈ (¬ p ∨₁ ¬ q))
  deM₁ = {!!}

  deM₂ : Tbool₁ ⊢ (⋀ ¬ (p ∨₁ q) ≈ (¬ p ∧₁ ¬ q))
  deM₂ = {!!}



-- another bool logic
data Σops₂ : List ⊤ × ⊤ → Set where
  t₂     : Σops₂ ([] ↦ tt)
  f₂     : Σops₂ ([] ↦ tt)
  or₂    : Σops₂ ((tt ∷ [ tt ]) ↦ tt)
  equiv₂ : Σops₂ ((tt ∷ [ tt ]) ↦ tt)


Σbool₂ : Signature
Σbool₂ = ⟨ ⊤ , Σops₂ ⟩

Vars₂ : Vars Σbool₂
Vars₂ s = ℕ


Eq₂ : Set
Eq₂ = Equation Σbool₂ Vars₂ tt

open TermAlgebra
open Signature
open import HeterogenuousVec

-- A formula is a term of the Term Algebra
Form₂ : Set
Form₂ = HU (Σbool₂ 〔 Vars₂ 〕) tt

-- smart constructors
_∨₂_ : Form₂ → Form₂ → Form₂
φ ∨₂ ψ = term or₂ ⟨⟨ φ , ψ ⟩⟩

_≡₂_ : Form₂ → Form₂ → Form₂
φ ≡₂ ψ = term equiv₂ ⟨⟨ φ , ψ ⟩⟩

p~ : Form₂
p~ = term (inj₂ 0) ⟨⟩

q~ : Form₂
q~ = term (inj₂ 1) ⟨⟩

r~ : Form₂
r~ = term (inj₂ 2) ⟨⟩

true₂ : Form₂
true₂ = term (inj₁ t₂) ⟨⟩

false₂ : Form₂
false₂ = term (inj₁ f₂) ⟨⟩

-- Axioms
assocEquiv₂ : Eq₂
assocEquiv₂ = ⋀ p~ ≡₂ (q~ ≡₂ r~) ≈ ((p~ ≡₂ q~) ≡₂ r~)

commEquiv₂ : Eq₂
commEquiv₂ = ⋀ p~ ≡₂ q~ ≈ (q~ ≡₂ p~)

assocOr₂ : Eq₂
assocOr₂ = ⋀ p~ ∨₂ (q~ ∨₂ r~) ≈ ((p~ ∨₂ q~) ∨₂ r~)

commOr₂ : Eq₂
commOr₂ = ⋀ p~ ∨₂ q~ ≈ (q~ ∨₂ p~)

neuEquiv : Eq₂
neuEquiv = ⋀ p~ ≡₂ true₂ ≈ p~

reflEquiv : Eq₂
reflEquiv = ⋀ p~ ≡₂ p~ ≈ true₂

absOr : Eq₂
absOr = ⋀ p~ ∨₂ true₂ ≈ true₂

neuOr : Eq₂
neuOr = ⋀ p~ ∨₂ false₂ ≈ p~

idemOr₂ : Eq₂
idemOr₂ = ⋀ p~ ∨₂ p~ ≈ p~

distOrEquiv : Eq₂
distOrEquiv = ⋀ p~ ∨₂ (q~ ≡₂ r~) ≈ ((p~ ∨₂ q~) ≡₂ (p~ ∨₂ r~)) 

Tbool₂ : Theory Σbool₂ Vars₂ (repeat tt 10)
Tbool₂ = assocEquiv₂ ▹ commEquiv₂ ▹ assocOr₂ ▹
         commOr₂ ▹ neuEquiv ▹ reflEquiv ▹
         absOr ▹ neuOr ▹ idemOr₂ ▹
         distOrEquiv ▹ ⟨⟩
