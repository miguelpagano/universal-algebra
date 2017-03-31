module EqBool1 where

open import UnivAlgebra
open import Equational
open import AlgTransf
open import Data.Unit hiding (setoid)
open import Data.List
open import Data.Product
open import Data.Nat
open import Data.Sum
open import HeterogenuousVec



repeat : ∀ {A : Set} → A → ℕ → List A
repeat a zero = []
repeat a (suc n) = a ∷ repeat a n

data Σops₁ : List ⊤ × ⊤ → Set where
  t₁   : Σops₁ ([] ↦ tt)
  f₁   : Σops₁ ([] ↦ tt)
  neg₁ : Σops₁ ([ tt ] ↦ tt)
  and₁ : Σops₁ ((tt ∷ [ tt ]) ↦ tt)
  or₁  : Σops₁ ((tt ∷ [ tt ]) ↦ tt)


Σbool₁ : Signature
Σbool₁ = record { sorts = ⊤ ; ops = Σops₁ }

open Signature

module Theory₁ where

  Vars₁ : Vars Σbool₁
  Vars₁ s = ℕ

  Eq₁ : Set
  Eq₁ = Equation Σbool₁ Vars₁ tt

  open TermAlgebra

  
  -- A formula is a term of the Term Algebra
  Form₁ : Set
  Form₁ = HU (Σbool₁ 〔 Vars₁ 〕) tt


  module Smartcons where
    -- smart constructors
    _∧_ : Form₁ → Form₁ → Form₁
    φ ∧ ψ = term and₁ ⟨⟨ φ , ψ ⟩⟩

    _∨_ : Form₁ → Form₁ → Form₁
    φ ∨ ψ = term or₁ ⟨⟨ φ , ψ ⟩⟩
  
    ¬ : Form₁ → Form₁
    ¬ φ = term neg₁ ⟪ φ ⟫
  
    p : Form₁
    p = term (inj₂ 0) ⟨⟩
    
    q : Form₁
    q = term (inj₂ 1) ⟨⟩

    r : Form₁
    r = term (inj₂ 2) ⟨⟩

    true : Form₁
    true = term (inj₁ t₁) ⟨⟩

    false : Form₁
    false = term (inj₁ f₁) ⟨⟩

  open Smartcons

  -- Axioms
  assocAnd₁ : Eq₁
  assocAnd₁ = ⋀ p ∧ (q ∧ r) ≈ ((p ∧ q) ∧ r)

  commAnd₁ : Eq₁
  commAnd₁ = ⋀ p ∧ q ≈ (q ∧ p)

  assocOr₁ : Eq₁
  assocOr₁ = ⋀ p ∨ (q ∨ r) ≈ ((p ∨ q) ∨ r)

  commOr₁ : Eq₁
  commOr₁ = ⋀ p ∨ q ≈ (q ∨ p)

  idemAnd₁ : Eq₁
  idemAnd₁ = ⋀ p ∧ p ≈ p

  idemOr₁ : Eq₁
  idemOr₁ = ⋀ p ∨ p ≈ p

  distAndOr₁ : Eq₁
  distAndOr₁ = ⋀ p ∧ (q ∨ r) ≈ ((p ∧ q) ∨ (p ∧ r))

  distOrAnd₁ : Eq₁
  distOrAnd₁ = ⋀ p ∨ (q ∧ r) ≈ ((p ∨ q) ∧ (p ∨ r))

  n₁ : Eq₁
  n₁ = ⋀ p ∧ (p ∨ q) ≈ p

  n₂ : Eq₁
  n₂ = ⋀ p ∨ (p ∧ q) ≈ p

  andF : Eq₁
  andF = ⋀ p ∧ (¬ p) ≈ false

  orT : Eq₁
  orT = ⋀ p ∨ (¬ p) ≈ true

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




module Proofs₁ where
  open ProvSetoid
  open Theory₁
  open import Relation.Binary.EqReasoning (ProvSetoid Tbool₁ tt)
  open Subst {Σbool₁} {Vars₁}
  open Equation
  open Smartcons
  open TermAlgebra
  
  p₁ : Tbool₁ ⊢ (⋀ ¬ p ∧ p ≈ false)
  p₁ = begin
         ¬ p ∧ p
         ≈⟨ psubst ax₂ σ₁ ∼⟨⟩ ⟩
         p ∧ ¬ p
         ≈⟨ psubst ax₁₁ idSubst ∼⟨⟩ ⟩
         false
       ∎
    where σ₁ : Subst
          σ₁ 0 = ¬ p
          σ₁ 1 = p
          σ₁ n = term (inj₂ n) ⟨⟩

  p₂ : Tbool₁ ⊢ (⋀ false ≈ ¬ true)
  p₂ = {!!}

  deM₁ : Tbool₁ ⊢ (⋀ ¬ (p ∧ q) ≈ (¬ p ∨ ¬ q))
  deM₁ = {!!}

  deM₂ : Tbool₁ ⊢ (⋀ ¬ (p ∨ q) ≈ (¬ p ∧ ¬ q))
  deM₂ = {!!}



-- another bool logic
data Σops₂ : List ⊤ × ⊤ → Set where
  t₂     : Σops₂ ([] ↦ tt)
  f₂     : Σops₂ ([] ↦ tt)
  or₂    : Σops₂ ((tt ∷ [ tt ]) ↦ tt)
  equiv₂ : Σops₂ ((tt ∷ [ tt ]) ↦ tt)


Σbool₂ : Signature
Σbool₂ = record { sorts = ⊤ ; ops = Σops₂ }

module Theory₂ where
  open TermAlgebra

  Vars₂ : Vars Σbool₂
  Vars₂ s = ℕ

  Eq₂ : Set
  Eq₂ = Equation Σbool₂ Vars₂ tt

  -- A formula is a term of the Term Algebra
  Form₂ : Set
  Form₂ = HU (Σbool₂ 〔 Vars₂ 〕) tt

  module Smartcons where
  
    _∨_ : Form₂ → Form₂ → Form₂
    φ ∨ ψ = term or₂ ⟨⟨ φ , ψ ⟩⟩

    _≡_ : Form₂ → Form₂ → Form₂
    φ ≡ ψ = term equiv₂ ⟨⟨ φ , ψ ⟩⟩

    p : Form₂
    p = term (inj₂ 0) ⟨⟩

    q : Form₂
    q = term (inj₂ 1) ⟨⟩

    r : Form₂
    r = term (inj₂ 2) ⟨⟩

    true₂ : Form₂
    true₂ = term (inj₁ t₂) ⟨⟩

    false₂ : Form₂
    false₂ = term (inj₁ f₂) ⟨⟩


  open Smartcons
  -- Axioms
  assocEquiv : Eq₂
  assocEquiv = ⋀ p ≡ (q ≡ r) ≈ ((p ≡ q) ≡ r)

  commEquiv : Eq₂
  commEquiv = ⋀ p ≡ q ≈ (q ≡ p)

  assocOr : Eq₂
  assocOr = ⋀ p ∨ (q ∨ r) ≈ ((p ∨ q) ∨ r)

  commOr : Eq₂
  commOr = ⋀ p ∨ q ≈ (q ∨ p)

  neuEquiv : Eq₂
  neuEquiv = ⋀ p ≡ true₂ ≈ p

  reflEquiv : Eq₂
  reflEquiv = ⋀ p ≡ p ≈ true₂

  absOr : Eq₂
  absOr = ⋀ p ∨ true₂ ≈ true₂

  neuOr : Eq₂
  neuOr = ⋀ p ∨ false₂ ≈ p

  idemOr : Eq₂
  idemOr = ⋀ p ∨ p ≈ p

  distOrEquiv : Eq₂
  distOrEquiv = ⋀ p ∨ (q ≡ r) ≈ ((p ∨ q) ≡ (p ∨ r)) 

  Tbool₂ : Theory Σbool₂ Vars₂ (repeat tt 10)
  Tbool₂ = assocEquiv ▹ commEquiv ▹ assocOr ▹
           commOr ▹ neuEquiv ▹ reflEquiv ▹
           absOr ▹ neuOr ▹ idemOr ▹
           distOrEquiv ▹ ⟨⟩


module BoolModel₂ where

  open import Data.Bool
  open import Relation.Binary.PropositionalEquality as PE
  open import Relation.Binary
  open import Function.Equality hiding (setoid)

  BCarrier : sorts Σbool₁ → Setoid _ _
  BCarrier _ = setoid Bool

  Bops : ∀ {ar s} → (f : ops Σbool₂ (ar , s)) →
           BCarrier ✳ ar ⟶ BCarrier s
  Bops t₂ = record { _⟨$⟩_ = λ _ → true ; cong = λ _ → refl }
  Bops f₂ = record { _⟨$⟩_ = λ _ → false ; cong = λ _ → refl }
  Bops or₂ = record { _⟨$⟩_ = λ { ⟨⟨ b , b' ⟩⟩ → b ∨ b' } ;
                      cong = λ { {⟨⟨ b₀ , b₀' ⟩⟩} {⟨⟨ b₁ , b₁' ⟩⟩}
                                 (∼▹ b₀≡b₁ (∼▹ b₀'≡b₁' ∼⟨⟩)) →
                                                     cong₂ _∨_ b₀≡b₁ b₀'≡b₁' } }
  Bops equiv₂ = record { _⟨$⟩_ = λ { ⟨⟨ b , b' ⟩⟩ → b =b b' } ;
                      cong = λ { {⟨⟨ b₀ , b₀' ⟩⟩} {⟨⟨ b₁ , b₁' ⟩⟩}
                                 (∼▹ b₀≡b₁ (∼▹ b₀'≡b₁' ∼⟨⟩)) →
                                                    cong₂ _=b_ b₀≡b₁ b₀'≡b₁' } }
    where _=b_ : Bool → Bool → Bool
          false =b b₂ = not b₂
          true  =b b₂ = b₂


  B₂ : Algebra Σbool₂
  B₂ = BCarrier ∥ Bops


module Translation where
  open import Function
  open import Data.Fin hiding (#_)
  open import Data.List renaming (map to lmap)

  open TermAlgebra
  open Algebra
  open FormalTerm Σbool₂

  ops↝ : ∀ {ar s} → (f : Σops₁ (ar ↦ s)) →
           lmap id ar ⊩ s
  ops↝ t₁ = t₂ ∣$∣ ⟨⟩
  ops↝ f₁ = f₂ ∣$∣ ⟨⟩
  ops↝ or₁ = or₂ ∣$∣ ⟨⟨ p , q ⟩⟩ 
    where p = # zero
          q = # (suc zero)
  ops↝ neg₁ = equiv₂ ∣$∣ ⟨⟨ p , false ⟩⟩
    where p = # zero
          false = f₂ ∣$∣ ⟨⟩
  ops↝ and₁ = equiv₂ ∣$∣ ⟨⟨ equiv₂ ∣$∣ ⟨⟨ p , q ⟩⟩
                         , or₂ ∣$∣ ⟨⟨ p , q ⟩⟩ ⟩⟩
    where p = # zero
          q = # (suc zero)

  Σtrans : Σbool₁ ↝ Σbool₂
  Σtrans = record { ↝ₛ = id
                  ; ↝ₒ = ops↝
                  }

  open AlgTrans Σtrans
  open BoolModel₂
  
  -- Bool es álgebra de Σbool₁
  B₁ : Algebra Σbool₁
  B₁ = 〈  B₂ 〉

  open Theory₁
  open Theory₂

  -- Tbool₂ implica a Tbool₁:
  open TheoryTrans Σtrans Vars₁ Vars₂ id

  T₂⇒T₁ : Tbool₂ ⇒T Tbool₁
  T₂⇒T₁ = ?

