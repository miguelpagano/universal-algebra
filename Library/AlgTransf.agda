module AlgTransf where

open import Setoids
open import UnivAlgebra

open import Relation.Binary
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Nat renaming (_⊔_ to _⊔ₙ_)
open import Data.Product renaming (map to pmap)
open import Function
open import Function.Equality renaming (_∘_ to _∘ₛ_) hiding (id)
open import Data.Bool hiding (T)
open import Data.List renaming (map to lmap)
open import Relation.Binary.PropositionalEquality as PE
open import Induction.WellFounded
open import Data.String
open import Data.Fin hiding (#_)
open import HeterogenuousVec

open Signature
open Algebra

module FormalTerm (Σ : Signature) where

 data _⊩_  (ar' : Arity Σ) : (sorts Σ) → Set where
   #   : (n : Fin (length ar')) → ar' ⊩ (ar' ‼ n)
   _∣$∣_ : ∀ {ar s} → ops Σ (ar , s) → 
               HVec (ar' ⊩_) ar → ar' ⊩ s


module FormalTermInt {ℓ₁ ℓ₂} {Σ : Signature} (A : Algebra {ℓ₁} {ℓ₂} Σ) where
  open FormalTerm Σ
  mutual

    ⟦_⟧⊩ : ∀ {ar s} → ar ⊩ s → A ⟦ ar ⟧ₛ* → ∥ A ⟦ s ⟧ₛ ∥
    ⟦ # n ⟧⊩    as =  as ‼v n
    ⟦ f ∣$∣ ts ⟧⊩  as = A ⟦ f ⟧ₒ ⟨$⟩ ⟦ ts ⟧⊩* as


    ⟦_⟧⊩* : ∀ {ar ar'} → HVec (ar ⊩_) ar' → A ⟦ ar ⟧ₛ* → A ⟦ ar' ⟧ₛ*
    ⟦ ⟨⟩ ⟧⊩*      as = ⟨⟩
    ⟦ t ▹ ts ⟧⊩*  as = ⟦ t ⟧⊩ as ▹ ⟦ ts ⟧⊩* as 


  cong⟦⟧⊩ : ∀ {ar s} {vs vs' : A ⟦ ar ⟧ₛ* } →
            (t : ar ⊩ s) →
            _∼v_  {R = Setoid._≈_ ∘ _⟦_⟧ₛ A} vs vs' →
            Setoid._≈_ (A ⟦ s ⟧ₛ) (⟦ t ⟧⊩ vs) (⟦ t ⟧⊩ vs')
  cong⟦⟧⊩ {vs = vs} {vs'} (# n) eq = ~v-pointwise vs vs' eq n
  cong⟦⟧⊩ {ar} {_} {vs} {vs'} (f ∣$∣ ts) eq = Π.cong (A ⟦ f ⟧ₒ) (cong⟦⟧⊩* ts)
    where  cong⟦⟧⊩* : ∀ {ar'} →
                   (ts : HVec (ar ⊩_) ar') →
                   (⟦ ts ⟧⊩* vs ) ∼v (⟦ ts ⟧⊩* vs' )
           cong⟦⟧⊩* ⟨⟩ = ∼⟨⟩
           cong⟦⟧⊩* (t ▹ ts) = ∼▹ (cong⟦⟧⊩ t eq) (cong⟦⟧⊩* ts)


record _↝_ (Σₛ Σₜ : Signature) : Set where
 open FormalTerm Σₜ
 field
  ↝ₛ : sorts Σₛ → sorts Σₜ
  ↝ₒ : ∀ {ar s}  → ops Σₛ (ar , s) → lmap ↝ₛ ar ⊩ ↝ₛ s


module AlgTrans {Σₛ Σₜ} (t : Σₛ ↝ Σₜ) where

  open _↝_
  open FormalTerm Σₜ

  _⟨_⟩ₛ : ∀  {ℓ₀ ℓ₁} → (A : Algebra {ℓ₀} {ℓ₁} Σₜ) →
             (s : sorts Σₛ) → Setoid _ _
  A ⟨ s ⟩ₛ = A ⟦ ↝ₛ t s ⟧ₛ

  _⟨_⟩ₒ :  ∀  {ℓ₀ ℓ₁ ar s} → (A : Algebra {ℓ₀} {ℓ₁} Σₜ) →
              ops Σₛ (ar , s) →
              (A ⟨_⟩ₛ) ✳ ar ⟶  A ⟨ s ⟩ₛ
  A ⟨ f ⟩ₒ = record  {  _⟨$⟩_ = ⟦ ↝ₒ t f ⟧⊩ ∘ reindex (↝ₛ t) 
                    ;  cong =  cong⟦⟧⊩ (↝ₒ t f) ∘ ∼v-reindex (↝ₛ t)
                    }
    where open FormalTermInt A

  〈_〉 : ∀ {ℓ₀ ℓ₁} → Algebra {ℓ₀} {ℓ₁} Σₜ → Algebra Σₛ
  〈 A 〉 =  (A ⟨_⟩ₛ) ∥ ((A ⟨_⟩ₒ))


module HomoTrans {Σₛ Σₜ}  {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
                 (t : Σₛ ↝ Σₜ)
                 (A : Algebra {ℓ₁} {ℓ₂} Σₜ)
                 (A' : Algebra {ℓ₃} {ℓ₄} Σₜ) where 

  open Hom
  open Homo
  open FormalTerm Σₜ
  open AlgTrans t
  open _↝_
  
  hcond↝ : ∀ {l₀ l₁ l₂ l₃}
             {A : Algebra {l₀} {l₁} Σₜ}
             {A' : Algebra {l₂} {l₃} Σₜ}
             {ty : Type Σₛ} → (h : Homo A A') → 
             (f : ops Σₛ ty) → homCond 〈 A 〉 〈 A' 〉 (′ h ′ ∘ ↝ₛ t) f 
  hcond↝  {A = A} {A'} {ar ↦ s} h f as = 
                       subst (λ vec → Setoid._≈_ (A' ⟦ ↝ₛ t s ⟧ₛ)
                                    (′ h ′ (↝ₛ t s) ⟨$⟩
                                           ⟦_⟧⊩ A (↝ₒ t f) (reindex (↝ₛ t) as))
                                    (⟦_⟧⊩ A' (↝ₒ t f) vec) 
                                    )
                       (mapReindex (↝ₛ t) 
                                   (_⟨$⟩_ ∘ ′ h ′)  as)
                       (homCond↝' (lmap (↝ₛ t) ar) (↝ₛ t s) (↝ₒ t f)
                                  (reindex (↝ₛ t) as))

    where open FormalTermInt
          homCond↝' : (ar' : Arity Σₜ) → (s' : sorts Σₜ) → (e : ar' ⊩ s') →
                      (vs : A ⟦ ar' ⟧ₛ* ) →                   
                      Setoid._≈_ (_⟦_⟧ₛ A' s')
                                 (′ h ′ s' ⟨$⟩ ⟦_⟧⊩ A e vs)
                                 (⟦ A' ⟧⊩ e (map⟿ A A' ′ h ′ vs))
          homCond↝' [] _ (# ()) ⟨⟩                           
          homCond↝' (s ∷ ar) .s (# zero) (v ▹ vs) = Setoid.refl (A' ⟦ s ⟧ₛ)
          homCond↝' (s ∷ ar) .(ar ‼ n) (# (suc n)) (v ▹ vs) =
                                                 homCond↝' ar (ar ‼ n) (# n) vs
          homCond↝' ar s (_∣$∣_ {ar₁} f₁ es) vs =
                    Setoid.trans (A' ⟦ s ⟧ₛ) (cond h f₁ (⟦_⟧⊩* A es vs))
                                             (Π.cong (A' ⟦ f₁ ⟧ₒ)
                                                     (homCond↝'vec ar₁ es))
            where homCond↝'vec : (ar₁ : Arity Σₜ) → 
                                  (es : HVec (_⊩_ ar) ar₁) → 
                                    _∼v_ {R = Setoid._≈_ ∘ (A' ⟦_⟧ₛ) }
                                      (map (λ x → _⟨$⟩_ (′ h ′ x)) (⟦_⟧⊩* A es vs))
                                      (⟦_⟧⊩* A' es (map (λ x → _⟨$⟩_ (′ h ′ x)) vs))
                  homCond↝'vec .[] ⟨⟩ = ∼⟨⟩
                  homCond↝'vec (s₁ ∷ ar₁) (e ▹ es) = ∼▹ (homCond↝' ar s₁ e vs)
                                                        (homCond↝'vec ar₁ es)
  〈_〉ₕ : Homo A A' → Homo 〈 A 〉 〈 A' 〉
  〈 h 〉ₕ = record  { ′_′ = ′ h ′ ∘ ↝ₛ t
                   ; cond = hcond↝ h
                   }

import Relation.Binary.EqReasoning as EqR

-- Translation and Equational logic
open import Equational
open _↝_
module TheoryTrans {Σₛ Σₜ : Signature} (Σ↝ : Σₛ ↝ Σₜ)
                   (Xₛ : Vars Σₛ) (Xₜ : Vars Σₜ)
                   (tvars : ∀ {s} → Xₛ s → Xₜ (↝ₛ Σ↝ s)) where


  open Hom
  open AlgTrans Σ↝
  open import Data.Sum hiding (map)
  open import Data.Product renaming (map to pmap)

  -- Terms translation
  term↝ : Homo (T Σₛ 〔 Xₛ 〕) 〈 T Σₜ 〔 Xₜ 〕 〉
  term↝ = TΣXHom
    where open TermAlgebra (Σₜ 〔 Xₜ 〕)
          θv : Env {X = Xₛ} 〈 T Σₜ 〔 Xₜ 〕 〉
          θv {s} v = term (inj₂ (tvars v)) ⟨⟩
          open InitHomoExt 〈 T Σₜ 〔 Xₜ 〕 〉 θv

  open Homo
  
  -- Equations translation
  eq↝ : ∀ {s} → Equation Σₛ Xₛ s → Equation Σₜ Xₜ (↝ₛ Σ↝ s)
  eq↝ {s} (⋀ t ≈ t' if「 carty 」 cond) =
           ⋀ ′ term↝ ′ s ⟨$⟩ t ≈ ′ term↝ ′ s ⟨$⟩ t'
                     if「 lmap (↝ₛ Σ↝) carty 」 (eq↝vec carty cond)
    where open TermAlgebra (Σₜ 〔 Xₜ 〕) renaming (∣T∣ to ∣T∣ₜ)
          open TermAlgebra (Σₛ 〔 Xₛ 〕) renaming (∣T∣ to ∣T∣ₛ)
          eq↝vec : (ar : Arity Σₛ) →
                    HVec (λ s' → ∥ ∣T∣ₛ ⟦ s' ⟧ₛ ∥) ar ×
                    HVec (λ s' → ∥ ∣T∣ₛ ⟦ s' ⟧ₛ ∥) ar →
                    HVec (λ s' → ∥ ∣T∣ₜ ⟦ s' ⟧ₛ ∥) (lmap (↝ₛ Σ↝) ar) ×
                    HVec (λ s' → ∥ ∣T∣ₜ ⟦ s' ⟧ₛ ∥) (lmap (↝ₛ Σ↝) ar)
          eq↝vec [] (⟨⟩ , ⟨⟩) = ⟨⟩ , ⟨⟩
          eq↝vec (s₀ ∷ is) (t₀ ▹ ts , t₀' ▹ ts') =
                           ((′ term↝ ′ s₀ ⟨$⟩ t₀) ▹ proj₁ (eq↝vec is (ts , ts'))) ,
                           ((′ term↝ ′ s₀ ⟨$⟩ t₀') ▹ proj₂ (eq↝vec is (ts , ts')))

  -- Theory implication
  _⇒T~_ : ∀ {ar ar'} → Theory Σₜ Xₜ ar → Theory Σₛ Xₛ ar' → Set
  Tₜ ⇒T~ Tₛ = ∀ {s} {ax : Equation Σₛ Xₛ s} → ax ∈ Tₛ → Tₜ ⊢ eq↝ ax

  -- Importante: Nuestro sistema de pruebas sólo permite demostrar ecuaciones no condicionales.
  -- Si tenemos axiomas con condiciones, entonces no podríamos probarlos en la otra teoría.


  -- Model translation
  module ModelTrans {ar : Arity Σₛ} {ar' : Arity Σₜ}
                    (Thₛ : Theory Σₛ Xₛ ar) (Thₜ : Theory Σₜ Xₜ ar')
                    (p⇒ : Thₜ ⇒T~ Thₛ) where


    open Setoid


    module Lemma₀ {ℓ₁ ℓ₂ : Level}
                  (A : Algebra {ℓ₁} {ℓ₂} Σₜ)
                  (θ : Env {X = Xₜ} A) where
                  

      open InitHomoExt A θ renaming (TΣXHom to ∣H∣ₜ)
      
      θ↝ : Env {X = Xₛ} 〈 A 〉
      θ↝ {s} v = θ (tvars v)

      open InitHomoExt 〈 A 〉 θ↝ renaming (TΣXHom to ∣H∣ₛ ; tot to totₛ ; HomEnv to HomEnvₛ)

      private _∼ : (s : sorts Σₛ) → sorts Σₜ
      s ∼ = ↝ₛ Σ↝ s

      open TermAlgebra Σₛ
      open FormalTerm Σₜ
      open HomoTrans Σ↝ (T Σₜ 〔 Xₜ 〕) A
      open HomComp

      lemma₀ : ∀ {s} → (t : ∥ (T Σₛ 〔 Xₛ 〕) ⟦ s ⟧ₛ ∥) →
                     _≈_ (〈 A 〉 ⟦ s ⟧ₛ) ((′ 〈 ∣H∣ₜ 〉ₕ ′ s) ⟨$⟩ (′ term↝ ′ s ⟨$⟩ t))
                                        ((′ ∣H∣ₛ ′ s) ⟨$⟩ t)
      lemma₀ {s} t = totₛ (〈 ∣H∣ₜ 〉ₕ ∘ₕ term↝) ∣H∣ₛ he₁ he₂ s t
        where he₁ : HomEnvₛ (〈 ∣H∣ₜ 〉ₕ ∘ₕ term↝)
              he₁ s x = Setoid.refl (A ⟦ s ∼ ⟧ₛ)
              he₂ : HomEnvₛ ∣H∣ₛ
              he₂ s x = Setoid.refl (A ⟦ s ∼ ⟧ₛ)


    -- lemma : ∀ {s ℓ₁ ℓ₂} → (e : Equation Σₛ Xₛ s) → (A : Algebra {ℓ₁} {ℓ₂} Σₜ) →
    --                        A ⊨ (eq↝ e) → 〈 A 〉 ⊨ e
    -- lemma {s} (⋀ t ≈ t' if「 carty 」 cond) A sat θ eq = 
    --           begin
    --             (θ ↪) t
    --            ≈⟨ {!!} ⟩
    --             (θ ↪) t'
    --            ∎
    --   where open EqR (A ⟦ ↝ₛ Σ↝ s ⟧ₛ)
    --         open EnvExt 〈 A 〉

    -- ⊨T↝ : ∀ {ℓ₁ ℓ₂} → (A : Algebra {ℓ₁} {ℓ₂} Σₜ) → ⊨T Thₜ A → ⊨T Thₛ 〈 A 〉
    -- ⊨T↝ A record { satAll = satAll } =
    --              record { satAll = λ {s} {e} ax θ x₁ →
    --                        lemma e A (correctness (p⇒ ax) A (record { satAll = satAll })) θ x₁
    --                      }

