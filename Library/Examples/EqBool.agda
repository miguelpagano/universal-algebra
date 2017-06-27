{- Definition of two boolean theories and a translation
   from one of them to the another. The theories are
   T_Bool and T_DS from the article "Theorem Proving Modulo
   Based on Boolean Equational Procedures", Camilo Rocha
   and José Meseguer. -}
module Examples.EqBool where

open import UnivAlgebra
open import Morphisms
open import Equational
open import SigMorphism
import TermAlgebra
open import Data.Unit hiding (setoid)
open import Data.List
open import Data.Product
open import Data.Nat
open import Data.Sum
open import HeterogeneousVec
open import Relation.Binary.PropositionalEquality using (refl)


{- Example of equational logic: Theories for boolean algebras -}

{- Theory 1: The traditional Boolean theory -}
data Σops₁ : List ⊤ × ⊤ → Set where
  t₁   : Σops₁ ([] ↦ tt)
  f₁   : Σops₁ ([] ↦ tt)
  neg₁ : Σops₁ ([ tt ] ↦ tt)
  and₁ : Σops₁ ((tt ∷ [ tt ]) ↦ tt)
  or₁  : Σops₁ ((tt ∷ [ tt ]) ↦ tt)

-- The signature is monosorted, so we have an unique sort tt : ⊤ (the unit type)

Σbool₁ : Signature
Σbool₁ = record { sorts = ⊤ ; ops = Σops₁ }

open Signature

{- Definition of the equational theory -}
module Theory₁ where

  {- We use natural number as variables -}
  Vars₁ : Vars Σbool₁
  Vars₁ s = ℕ

  Eq₁ : Set
  Eq₁ = Equation Σbool₁ Vars₁ tt

  open TermAlgebra

  -- Formulas are terms of the Term Algebra
  Form₁ : Set
  Form₁ = HU (Σbool₁ 〔 Vars₁ 〕) tt

  module Smartcons where
    {- We define smart constructors to define axioms more easily -}
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

  -- Equations for each axiom of the theory
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

  abs₁ : Eq₁
  abs₁ = ⋀ p ∧ (p ∨ q) ≈ p

  abs₂ : Eq₁
  abs₂ = ⋀ p ∨ (p ∧ q) ≈ p

  defF : Eq₁
  defF = ⋀ p ∧ (¬ p) ≈ false

  3excl : Eq₁
  3excl = ⋀ p ∨ (¬ p) ≈ true


  {- The theory is a vector with the 12 axioms -}
  Tbool₁ : Theory Σbool₁ Vars₁ (replicate 12 tt)
  Tbool₁ = assocAnd₁ ▹ commAnd₁ ▹ assocOr₁ ▹
           commOr₁ ▹ idemAnd₁ ▹ idemOr₁ ▹
           distAndOr₁ ▹ distOrAnd₁ ▹ abs₁ ▹
           abs₂ ▹ defF ▹ 3excl ▹ ⟨⟩

  {- An axiom of Tbool₁ is an element of the vector, so we need 
     to say where is each one in it. In order to have a more compact
     syntax, we define patterns. -}
  pattern axAssoc∧ = here
  pattern axComm∧ = there here
  pattern axAssoc∨₁ = there (there here)
  pattern axComm∨₁ = there (there (there here))
  pattern axIdem∧ = there (there (there (there here)))
  pattern axIdem∨₁ = there (there (there (there (there here))))
  pattern axDist∧∨ = there (there (there (there (there (there here)))))
  pattern axDist∨∧ = there (there (there (there (there (there (there here))))))
  pattern axAbs₁ = there (there (there (there (there (there (there (there here)))))))
  pattern axAbs₂ = there (there (there (there (there (there (there
                                                          (there (there here))))))))
  pattern axDefF = there (there (there (there (there (there (there
                                                          (there (there (there here)))))))))
  pattern ax3excl = there (there (there (there (there (there (there
                                                          (there (there (there (there here))))))))))
  pattern noax₁ = there (there (there (there (there (there (there
                                                          (there (there (there (there (there ())))))))))))


{- Theory 2: Axiomatization of the propositional logic of Dijkstra-Scholten.
   We define the signature and a signature morphism from Σbool₁ to Σbool₂. 
   Then we define the axioms of Σbool₂ using variables coming from Σbool₁ (so
   we can transform a model of Σbool₂ in a model of Σbool₁ directly). -}
data Σops₂ : List ⊤ × ⊤ → Set where
  t₂     : Σops₂ ([] ↦ tt)
  f₂     : Σops₂ ([] ↦ tt)
  or₂    : Σops₂ ((tt ∷ [ tt ]) ↦ tt)
  equiv₂ : Σops₂ ((tt ∷ [ tt ]) ↦ tt)


Σbool₂ : Signature
Σbool₂ = record { sorts = ⊤ ; ops = Σops₂ }


{- We define signature morphism from Σbool₁ to Σbool₂ -}
module Translation where
  open import Function
  open import Data.Fin hiding (#_)
  open import Data.List renaming (map to lmap)

  open TermAlgebra
  open Algebra
  open FormalTerm Σbool₂

  {- For each operation of Σbool₁, we define a
     formal term in Σbool₂ -}
  ops↝ : ∀ {ar s} → (f : Σops₁ (ar ↦ s)) →
           lmap id ar ⊩ s
  ops↝ t₁ = t₂ ∣$∣ ⟨⟩
  ops↝ f₁ = f₂ ∣$∣ ⟨⟩
  ops↝ or₁ = or₂ ∣$∣ ⟨⟨ p , q ⟩⟩ 
    where p = # zero
          q = # (suc zero)
  -- ¬ p is translated to p ≡ false
  ops↝ neg₁ = equiv₂ ∣$∣ ⟨⟨ p , false ⟩⟩
    where p = # zero
          false = f₂ ∣$∣ ⟨⟩
  -- p ∧ q is translated to  (p ≡ q) ≡ p ∨ q
  ops↝ and₁ = equiv₂ ∣$∣ ⟨⟨ equiv₂ ∣$∣ ⟨⟨ p , q ⟩⟩
                         , or₂ ∣$∣ ⟨⟨ p , q ⟩⟩ ⟩⟩
    where p = # zero
          q = # (suc zero)

  Σtrans : Σbool₁ ↝ Σbool₂
  Σtrans = record { ↝ₛ = id
                  ; ↝ₒ = ops↝
                  }

open Translation

{- We define now a Σbool₂-theory using variables from Σbool₁ -}
module Theory₂ where
  open TermAlgebra
  open Theory₁ using (Vars₁)
  open TermTrans Σtrans

  Vars₂ : Vars Σbool₂
  Vars₂ = Vars₁ ↝̬

  Eq₂ : Set
  Eq₂ = Equation Σbool₂ Vars₂ tt

  Form₂ : Set
  Form₂ = HU (Σbool₂ 〔 Vars₂ 〕) tt

  varp : Vars₂ tt
  varp = ((tt , refl) , 0)

  varq : Vars₂ tt
  varq = ((tt , refl) , 1)

  varr : Vars₂ tt
  varr = ((tt , refl) , 2)

  module Smartcons where
  
    _∨_ : Form₂ → Form₂ → Form₂
    φ ∨ ψ = term or₂ ⟨⟨ φ , ψ ⟩⟩

    _≡_ : Form₂ → Form₂ → Form₂
    φ ≡ ψ = term equiv₂ ⟨⟨ φ , ψ ⟩⟩

    p : Form₂
    p = term (inj₂ varp) ⟨⟩

    q : Form₂
    q = term (inj₂ varq) ⟨⟩

    r : Form₂
    r = term (inj₂ varr) ⟨⟩

    true₂ : Form₂
    true₂ = term (inj₁ t₂) ⟨⟩

    false₂ : Form₂
    false₂ = term (inj₁ f₂) ⟨⟩


  open Smartcons
  -- Equations for each axiom
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

  Tbool₂ : Theory Σbool₂ Vars₂ (replicate 10 tt)
  Tbool₂ = assocEquiv ▹ commEquiv ▹ assocOr ▹
           commOr ▹ neuEquiv ▹ reflEquiv ▹
           absOr ▹ neuOr ▹ idemOr ▹
           distOrEquiv ▹ ⟨⟩


  {- Patterns for each axiom in Tbool₂ -}

  pattern axAssoc≡ = here
  pattern axComm≡ = there here
  pattern axAssoc∨ = there (there here)
  pattern axComm∨ = there (there (there here))
  pattern axNeu≡ = there (there (there (there here)))
  pattern axRefl≡ = there (there (there (there (there here))))
  pattern axAbs∨ = there (there (there (there (there (there here)))))
  pattern axNeu∨ = there (there (there (there (there (there (there here))))))
  pattern axIdem∨ = there (there (there (there (there (there (there (there here)))))))
  pattern axDist∨≡ = there (there (there (there (there (there (there
                                                          (there (there here))))))))
  pattern noax = there (there (there (there (there (there (there
                                                          (there (there (there ())))))))))



  {- Tbool₂ implies Tbool₁ -}
  module Tbool₂⇒Tbool₁ where
    open Theory₁
    open TheoryTrans Σtrans Vars₁
    open ProvSetoid
    open import Relation.Binary.EqReasoning (ProvSetoid Tbool₂ tt)

  
    {- We have to proof each axiom of
      Tbool₁ in theory Tbool₂ -}

    open Subst

    T₂⊢idem∨ : Tbool₂ ⊢ eq↝ idemOr₁
    T₂⊢idem∨ =
      begin
        p ∨ p
      ≈⟨ psubst axIdem∨ idSubst ∼⟨⟩ ⟩
        p
      ∎

    T₂⊢assoc∧ : Tbool₂ ⊢ eq↝ assocAnd₁
    T₂⊢assoc∧ =
      begin
        {!!}
      ≈⟨ {!!} ⟩
        {!!}
      ∎
    
    T₂⊢idem∧ : Tbool₂ ⊢ eq↝ idemAnd₁
    T₂⊢idem∧ =
      begin
        ((p ≡ p) ≡ (p ∨ p))
      ≈⟨ preemp (∼▹ (psubst axRefl≡ idSubst ∼⟨⟩) (∼▹ prefl ∼⟨⟩)) equiv₂ ⟩
        (true₂ ≡ (p ∨ p))
      ≈⟨ preemp (∼▹ prefl (∼▹ ((psubst axIdem∨ idSubst ∼⟨⟩)) ∼⟨⟩)) equiv₂ ⟩
        (true₂ ≡ p)
      ≈⟨ psubst axComm≡ σ ∼⟨⟩ ⟩
        (p ≡ true₂)
      ≈⟨ psubst axNeu≡ idSubst ∼⟨⟩ ⟩
        p
      ∎
      where σ : Subst
            σ ( _ , 0 ) = true₂
            σ ( _ , 1 ) = p
            σ n = term (inj₂ n) ⟨⟩
    
    T₂⇒T₁ : Tbool₂ ⇒T~ Tbool₁
    T₂⇒T₁ axAssoc∧ = T₂⊢assoc∧
    T₂⇒T₁ axComm∧ = {!!}
    T₂⇒T₁ axAssoc∨₁ = {!!}
    T₂⇒T₁ axComm∨₁ = {!!}
    T₂⇒T₁ axIdem∧ = T₂⊢idem∧
    T₂⇒T₁ axIdem∨₁ = T₂⊢idem∨
    T₂⇒T₁ axDist∧∨ = {!!}
    T₂⇒T₁ axDist∨∧ = {!!}
    T₂⇒T₁ axAbs₁ = {!!}
    T₂⇒T₁ axAbs₂ = {!!}
    T₂⇒T₁ axDefF = {!!}
    T₂⇒T₁ ax3excl = {!!}
    T₂⇒T₁ noax₁

-- Bool is model of Tbool₂
module BoolModel₂ where

  open import Data.Bool
  open import Relation.Binary.PropositionalEquality as PE
  open import Relation.Binary
  open import Function.Equality hiding (setoid)

  BCarrier : sorts Σbool₁ → Setoid _ _
  BCarrier _ = setoid Bool

  _=b_ : Bool → Bool → Bool
  false =b b₂ = not b₂
  true  =b b₂ = b₂

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


  B₂ : Algebra Σbool₂
  B₂ = BCarrier ∥ Bops

  open Theory₂

  B₂⊨assoc≡ : B₂ ⊨ assocEquiv
  B₂⊨assoc≡ θ ∼⟨⟩ with θ varp | θ varq | θ varr
  B₂⊨assoc≡ θ ∼⟨⟩ | true | b | c = refl
  B₂⊨assoc≡ θ ∼⟨⟩ | false | true | c = refl
  B₂⊨assoc≡ θ ∼⟨⟩ | false | false | false = refl
  B₂⊨assoc≡ θ ∼⟨⟩ | false | false | true = refl


  B₂⊨comm≡ : B₂ ⊨ commEquiv
  B₂⊨comm≡ θ ∼⟨⟩ with θ varp | θ varq
  B₂⊨comm≡ θ ∼⟨⟩ | false | false = refl
  B₂⊨comm≡ θ ∼⟨⟩ | false | true = refl
  B₂⊨comm≡ θ ∼⟨⟩ | true | false = refl
  B₂⊨comm≡ θ ∼⟨⟩ | true | true = refl


  B₂⊨assoc∨ : B₂ ⊨ assocOr
  B₂⊨assoc∨ θ ∼⟨⟩ with θ varp | θ varq | θ varr
  B₂⊨assoc∨ θ ∼⟨⟩ | false | b | c = refl
  B₂⊨assoc∨ θ ∼⟨⟩ | true | b | c = refl

  B₂⊨comm∨ : B₂ ⊨ commOr
  B₂⊨comm∨ θ ∼⟨⟩ with θ varp | θ varq
  B₂⊨comm∨ θ ∼⟨⟩ | false | false = refl
  B₂⊨comm∨ θ ∼⟨⟩ | false | true = refl
  B₂⊨comm∨ θ ∼⟨⟩ | true | false = refl
  B₂⊨comm∨ θ ∼⟨⟩ | true | true = refl

  B₂⊨neu≡ : B₂ ⊨ neuEquiv
  B₂⊨neu≡ θ ∼⟨⟩ with θ varp
  B₂⊨neu≡ θ ∼⟨⟩ | false = refl
  B₂⊨neu≡ θ ∼⟨⟩ | true = refl

  B₂⊨refl≡ : B₂ ⊨ reflEquiv
  B₂⊨refl≡ θ ∼⟨⟩ with θ varp
  B₂⊨refl≡ θ ∼⟨⟩ | false = refl
  B₂⊨refl≡ θ ∼⟨⟩ | true = refl

  B₂⊨abs∨ : B₂ ⊨ absOr
  B₂⊨abs∨ θ ∼⟨⟩ with θ varp
  B₂⊨abs∨ θ ∼⟨⟩ | false = refl
  B₂⊨abs∨ θ ∼⟨⟩ | true = refl

  B₂⊨neu∨ : B₂ ⊨ neuOr
  B₂⊨neu∨ θ ∼⟨⟩ with θ varp
  B₂⊨neu∨ θ ∼⟨⟩ | false = refl
  B₂⊨neu∨ θ ∼⟨⟩ | true = refl

  B₂⊨idem∨ : B₂ ⊨ idemOr
  B₂⊨idem∨ θ ∼⟨⟩ with θ varp
  B₂⊨idem∨ θ ∼⟨⟩ | false = refl
  B₂⊨idem∨ θ ∼⟨⟩ | true = refl

  B₂⊨dist∨≡ : B₂ ⊨ distOrEquiv
  B₂⊨dist∨≡ θ ∼⟨⟩ with θ varp | θ varq | θ varr
  B₂⊨dist∨≡ θ ∼⟨⟩ | false | b | c = refl
  B₂⊨dist∨≡ θ ∼⟨⟩ | true | b | c = refl

  B₂model : B₂ ⊨T Tbool₂
  B₂model axAssoc≡ = B₂⊨assoc≡
  B₂model axComm≡ = B₂⊨comm≡
  B₂model axAssoc∨ = B₂⊨assoc∨
  B₂model axComm∨ = B₂⊨comm∨
  B₂model axNeu≡ = B₂⊨neu≡
  B₂model axRefl≡ = B₂⊨refl≡
  B₂model axAbs∨ = B₂⊨abs∨
  B₂model axNeu∨ = B₂⊨neu∨
  B₂model axIdem∨ = B₂⊨idem∨
  B₂model axDist∨≡ = B₂⊨dist∨≡
  B₂model noax




-- Bool is model Tbool₁
module BoolModel₁ where
  open import Data.Bool
  open ReductAlgebra Σtrans
  open BoolModel₂

  {- Instead of prove that Bool is model of Tbool₁ (i.e., 
     it satisfies each axiom) we obtain this model from
     B₂ via the reduct theorem -}
  
  B₁ : Algebra Σbool₁
  B₁ = 〈 B₂ 〉

  open Theory₁
  open Theory₂
  open Theory₂.Tbool₂⇒Tbool₁
  open TheoryTrans.ModelPreserv Σtrans Vars₁ Tbool₁
  --⊨T⇒↝
  B₁model : B₁ ⊨T Tbool₁
  B₁model = ⊨T⇒↝ Tbool₂ T₂⇒T₁ B₂ B₂model --⊨T⇒↝ Tbool₂ T₂⇒T₁ B₂
