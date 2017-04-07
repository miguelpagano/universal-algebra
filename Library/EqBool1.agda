module EqBool1 where

open import UnivAlgebra
open import Equational
open import AlgTransf
open import Data.Unit hiding (setoid)
open import Data.List
open import Data.Product
open import Data.Nat
open import Data.Sum
open import HeterogeneousVec



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

  form↝ : Form₁ → Form₂
  form↝ = {!′ term↝ '!}

  -- Tbool₂ implica a Tbool₁:
{-  open TheoryTrans Σtrans Vars₁ Vars₂ id

  T₂⇒T₁ : Tbool₂ ⇒T~ Tbool₁
  T₂⇒T₁ = {!!}
-}

module GoguenMeseguer where


  data sorts∼ : Set where
    bool : sorts∼
    a    : sorts∼

  data Σops∼ : List sorts∼ × sorts∼ → Set where
    t   : Σops∼ ([] ↦ bool)
    f   : Σops∼ ([] ↦ bool)
    neg : Σops∼ ([ bool ] ↦ bool)
    and∼ : Σops∼ ((bool ∷ [ bool ]) ↦ bool)
    or∼  : Σops∼ ((bool ∷ [ bool ]) ↦ bool)
    foo : Σops∼ ([ a ] ↦ bool)

  Σ∼ : Signature
  Σ∼ = record { sorts = sorts∼ ; ops = Σops∼ }


  open import Data.Empty
  open import Data.Unit
  Vars∼ : Vars Σ∼
  Vars∼ bool = ℕ
  Vars∼ a = ⊤

  Eq∼ : Set
  Eq∼ = Equation Σ∼ Vars∼ bool

  open TermAlgebra

  
  -- A formula is a term of the Term Algebra
  Form : Set
  Form = HU (Σ∼ 〔 Vars∼ 〕) bool

  aterm : Set
  aterm = HU (Σ∼ 〔 Vars∼ 〕) a

  module Smartcons where

    ¬ : Form → Form
    ¬ φ = term neg ⟪ φ ⟫

    _∨_ : Form → Form → Form
    φ ∨ ψ = term or∼ ⟨⟨ φ , ψ ⟩⟩

    _∧_ : Form → Form → Form
    φ ∧ ψ = term and∼ ⟨⟨ φ , ψ ⟩⟩

    fu : aterm → Form
    fu aₜ = term foo ⟪ aₜ ⟫

    b : Form
    b = term (inj₂ 0) ⟨⟩

    av : aterm
    av = term (inj₂ tt) ⟨⟩

    T : Form
    T = term (inj₁ t) ⟨⟩

    F : Form
    F = term (inj₁ f) ⟨⟩

  module Theory where
    open Smartcons
    -- Axioms
    notT : Eq∼
    notT = ⋀ ¬ T ≈ F
  
    notF : Eq∼
    notF = ⋀ ¬ F ≈ T
  
    3exc : Eq∼
    3exc = ⋀ b ∨ (¬ b) ≈ T

    b∧¬b : Eq∼
    b∧¬b = ⋀ b ∧ (¬ b) ≈ F

    idem∧ : Eq∼
    idem∧ = ⋀ b ∧ b ≈ b

    idem∨ : Eq∼
    idem∨ = ⋀ b ∨ b ≈ b

    fooax : Eq∼
    fooax = ⋀ fu av ≈ ¬ (fu av)

    Th : Theory Σ∼ Vars∼ (repeat bool 7)
    Th = notT ▹ notF ▹ 3exc ▹ b∧¬b ▹ idem∧ ▹ idem∨ ▹ fooax ▹ ⟨⟩

    pattern ax₁ = here
    pattern ax₂ = there here
    pattern ax₃ = there (there here)
    pattern ax₄ = there (there (there here))
    pattern ax₅ = there (there (there (there here)))
    pattern ax₆ = there (there (there (there (there here))))
    pattern ax₇ = there (there (there (there (there (there here)))))
    pattern noax = there (there (there (there (there (there (there ()))))))

  module Proof where
    open ProvSetoid
    open Theory
    open import Relation.Binary.EqReasoning (ProvSetoid Th bool)
    open Subst {Σ∼} {Vars∼}
    open Equation
    open Smartcons
    open TermAlgebra

  
    t≈f : Th ⊢ (⋀ T ≈ F)
    t≈f =
      begin
        T
      ≈⟨ psym (psubst ax₃ σ₁ ∼⟨⟩) ⟩
        (fu av ∨ (¬ (fu av)))
      ≈⟨ preemp ∼⟨⟨ prefl , psym (psubst ax₇ idSubst ∼⟨⟩) ⟩⟩∼ or∼ ⟩
        (fu av ∨ fu av)
      ≈⟨ psubst ax₆ σ₁ ∼⟨⟩ ⟩
        fu av
      ≈⟨ psym (psubst ax₅ σ₁ ∼⟨⟩) ⟩
        (fu av ∧ fu av)
      ≈⟨ preemp ∼⟨⟨ prefl , psubst ax₇ idSubst ∼⟨⟩ ⟩⟩∼ and∼ ⟩
        (fu av ∧ (¬ (fu av)))
      ≈⟨ psubst ax₄ σ₁ ∼⟨⟩ ⟩
        F
      ∎
      where σ₁ : Subst
            σ₁ {bool} 0 = fu av
            σ₁ {bool} (suc x) = term (inj₂ x) ⟨⟩
            σ₁ {a} tt = term (inj₂ tt) ⟨⟩


  -- Es verdad que contradice corrección? Parece que no.
  module NotCorrectness where
    open import Data.Bool
    open import Relation.Binary.PropositionalEquality as PE
    open import Relation.Binary
    open import Function.Equality hiding (setoid)
    open import Data.Empty

    isorts : sorts Σ∼ → Setoid _ _
    isorts bool = PE.setoid Bool
    isorts a = PE.setoid ⊥

    iops : ∀ {ar s} → (op : ops Σ∼ (ar ↦ s)) → isorts ✳ ar ⟶ isorts s
    iops t = record { _⟨$⟩_ = λ _ → true ; cong = λ _ → refl }
    iops f = record { _⟨$⟩_ = λ _ → false ; cong = λ _ → refl }
    iops neg = record { _⟨$⟩_ = λ { ⟪ b ⟫ → not b } ;
                        cong = λ { {b₀ ▹ ⟨⟩} {b₁ ▹ ⟨⟩} (∼▹ b₀≡b₁ _) → PE.cong not b₀≡b₁ } }
    iops and∼ = record { _⟨$⟩_ = λ { ⟨⟨ b , b' ⟩⟩ → b ∧ b' } ;
                      cong = λ { {⟨⟨ b₀ , b₀' ⟩⟩} {⟨⟨ b₁ , b₁' ⟩⟩}
                                 (∼▹ b₀≡b₁ (∼▹ b₀'≡b₁' ∼⟨⟩)) →
                                                     cong₂ _∧_ b₀≡b₁ b₀'≡b₁' } }
    iops or∼ = record { _⟨$⟩_ = λ { ⟨⟨ b , b' ⟩⟩ → b ∨ b' } ;
                      cong = λ { {⟨⟨ b₀ , b₀' ⟩⟩} {⟨⟨ b₁ , b₁' ⟩⟩}
                                 (∼▹ b₀≡b₁ (∼▹ b₀'≡b₁' ∼⟨⟩)) →
                                                     cong₂ _∨_ b₀≡b₁ b₀'≡b₁' } }
    iops foo = record { _⟨$⟩_ = λ { (() ▹ ⟨⟩) }
                      ; cong = λ { {() ▹ ⟨⟩} {noel₂ ▹ ⟨⟩} (∼▹ ₁≡₂ x) } }

    model : Algebra Σ∼
    model = isorts ∥ iops

    open Theory


    sat₁ : model ⊨ notT
    sat₁ θ _ = refl

    sat₂ : model ⊨ notT
    sat₂ θ _ = refl

    sat₃ : model ⊨ 3exc
    sat₃ θ _ with θ {bool} 0
    sat₃ θ x | false = refl
    sat₃ θ x | true = refl

    sat₄ : model ⊨ b∧¬b
    sat₄ θ _ with θ {bool} 0
    sat₄ θ x | false = refl
    sat₄ θ x | true = refl

    sat₅ : model ⊨ idem∧
    sat₅ θ _ with θ {bool} 0
    sat₅ θ x | false = refl
    sat₅ θ x | true = refl

    sat₆ : model ⊨ idem∨
    sat₆ θ _ with θ {bool} 0
    sat₆ θ x | false = refl
    sat₆ θ x | true = refl

    sat₇ : model ⊨ fooax
    sat₇ θ ∼⟨⟩ with (θ {a} tt)
    sat₇ θ ∼⟨⟩ | ()
    

    ismodel : model ⊨T Th
    ismodel = sat
      where sat : {s : sorts∼} {e : Equation _ Vars∼ s} → e ∈ Th → model ⊨ e
            sat ax₁ = sat₁
            sat ax₂ = λ θ _ → refl
            sat ax₃ = sat₃
            sat ax₄ = sat₄
            sat ax₅ = sat₅
            sat ax₆ = sat₆
            sat ax₇ = sat₇
            sat noax 


    -- para poder usar corrección deberíamos dar un entorno. Es decir
    -- una asignación de cada variable en los carriers del álgebra, pero
    -- no podemos dar una función que vaya de Vars (que es no vacío) a ⊥
    abs : true ≡ false
    abs = correctness t≈f model ismodel {!!} ∼⟨⟩
      where open Proof

