-- Universal Algebra Library
--
-- Signature morphisms: Derived signature morphism, reduct algebra,
--   reduct homomorphism, translation of terms and translation of
--   equational theories.
--

module SigMorphism where

open import Data.Bool hiding (T)
open import Data.Fin hiding (#_)
open import Data.List renaming (map to lmap;lookup to _‼_)
import Data.List.Properties as LP
open import Data.Nat renaming (_⊔_ to _⊔ₙ_)
open import Data.Product renaming (map to pmap)
open import Data.Sum hiding (map)
open import Function
open import Function.Equality renaming (_∘_ to _∘ₛ_) hiding (id)
open import Level renaming (suc to lsuc ; zero to lzero)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE
import Relation.Binary.EqReasoning as EqR

import Equational as Eq
open import HeterogeneousVec
open import Morphisms
open import Setoids hiding (∥_∥)
import TermAlgebra as T
open T using (Vars)
open import UnivAlgebra

module FormalTerm (Σ : Signature) where

 data _⊩_  (ar' : Arity Σ) : (sorts Σ) → Set where
   #   : (n : Fin (length ar')) → ar' ⊩ (ar' ‼ n)
   _∣$∣_ : ∀ {ar s} → ops Σ (ar , s) →
               HVec (ar' ⊩_) ar → ar' ⊩ s

 {- Lifting of indices -}
 mutual
   ↑ : ∀ {s} → (ar : Arity Σ) → (s' : sorts Σ) → ar ⊩ s → (s' ∷ ar) ⊩ s
   ↑ {.(ar ‼ n)} ar  s' (# n) = # (suc n)
   ↑ ar s' (x ∣$∣ x₁) = x ∣$∣ ↑* ar s' x₁

   ↑* : ∀ {ar'} → (ar : Arity Σ) → (s' : sorts Σ) → HVec (ar ⊩_) ar' → HVec ((s' ∷ ar) ⊩_) ar'
   ↑* ar s' ⟨⟩ = ⟨⟩
   ↑* ar s' (v ▹ vs) = (↑ ar s' v) ▹ (↑* ar s' vs)


 {- Substitution on formal terms -}
 mutual
   ⊩_/_ : {ar ar' : Arity Σ}  {s : sorts Σ} → ar ⊩ s → HVec (ar' ⊩_) ar → ar' ⊩ s
   ⊩_/_ {ar} {s = .(ar ‼ n)} (# n) ts' = ts' ‼v n
   ⊩ f ∣$∣ ts / ts' = f ∣$∣ (⊩* ts / ts')


   ⊩*_/_ : {ar ar' ar'' : Arity Σ} → HVec (ar ⊩_) ar'' → HVec (ar' ⊩_) ar → HVec (ar' ⊩_) ar''
   ⊩* ⟨⟩ / ts' = ⟨⟩
   ⊩* t ▹ ts / ts' = (⊩ t / ts') ▹ (⊩* ts / ts')

module FormalTermInt {ℓ₁ ℓ₂} {Σ : Signature} (A : Algebra {ℓ₁} {ℓ₂} Σ) where
  open FormalTerm Σ
  mutual

    ⟦_⟧⊩ : ∀ {ar s} → ar ⊩ s → A ∥ ar ∥* → A ∥ s ∥
    ⟦ # n ⟧⊩    as =  as ‼v n
    ⟦ f ∣$∣ ts ⟧⊩  as = A ⟦ f ⟧ₒ ⟨$⟩ ⟦ ts ⟧⊩* as


    ⟦_⟧⊩* : ∀ {ar ar'} → HVec (ar ⊩_) ar' → A ∥ ar ∥* → A ∥ ar' ∥*
    ⟦ ⟨⟩ ⟧⊩*      as = ⟨⟩
    ⟦ t ▹ ts ⟧⊩*  as = ⟦ t ⟧⊩ as ▹ ⟦ ts ⟧⊩* as


  cong⟦⟧⊩ : ∀ {ar s} {vs vs' : A ∥ ar ∥* } →
            (t : ar ⊩ s) →
            _∼v_  {R = ((Setoid._≈_ ∘ _⟦_⟧ₛ A) $-)} vs vs' →
            Setoid._≈_ (A ⟦ s ⟧ₛ) (⟦ t ⟧⊩ vs) (⟦ t ⟧⊩ vs')
  cong⟦⟧⊩ {vs = vs} {vs'} (# n) eq = ~v-pointwise eq n
  cong⟦⟧⊩ {ar} {_} {vs} {vs'} (f ∣$∣ ts) eq = Π.cong (A ⟦ f ⟧ₒ) (cong⟦⟧⊩* ts)
    where  cong⟦⟧⊩* : ∀ {ar'} →
                   (ts : HVec (ar ⊩_) ar') →
                   (⟦ ts ⟧⊩* vs ) ∼v (⟦ ts ⟧⊩* vs' )
           cong⟦⟧⊩* ⟨⟩ = ∼⟨⟩
           cong⟦⟧⊩* (t ▹ ts) = ∼▹ (cong⟦⟧⊩ t eq) (cong⟦⟧⊩* ts)


{- (derived) signature morphism -}
record _↝_ (Σₛ Σₜ : Signature) : Set where
 open FormalTerm Σₜ
 field
  ↝ₛ : sorts Σₛ → sorts Σₜ
  ↝ₒ : ∀ {ar s}  → ops Σₛ (ar , s) → lmap ↝ₛ ar ⊩ ↝ₛ s

{- Extension of signature morfisms to formal terms -}
module SigMorTerms {Σ₁ Σ₂ : Signature} where
    open FormalTerm
    open _↝_
    _⊩₁_ : Arity Σ₁ → sorts Σ₁ → Set
    _⊩₁_ = _⊩_ Σ₁
    _⊩₂_ : Arity Σ₂ → sorts Σ₂ → Set
    _⊩₂_ = _⊩_ Σ₂
    ⊩₂_/_ : _
    ⊩₂_/_ = ⊩_/_ Σ₂
    mutual
      _↝f_ : ∀ {ar : Arity Σ₁} {s} → (m : Σ₁ ↝ Σ₂) → ar ⊩₁ s →  lmap (↝ₛ m) ar ⊩₂ ↝ₛ m s
      _↝f_ {[]} m (# ())
      _↝f_ {_ ∷ _} m (# zero) = # zero
      _↝f_ {s ∷ ar} m (# (suc n)) = ↑ Σ₂  (lmap (↝ₛ m) ar) (↝ₛ m s) (m ↝f (# n))
      m ↝f (f ∣$∣ xs) = ⊩₂ (↝ₒ m f) / (m ↝f* xs)

      _↝f*_ : ∀ {ar ar' : Arity Σ₁} → (m : Σ₁ ↝ Σ₂) → HVec (ar ⊩₁_) ar' → HVec (lmap (↝ₛ m) ar ⊩₂_) (lmap (↝ₛ m) ar')
      m ↝f* ⟨⟩ = ⟨⟩
      m ↝f* (v ▹ vs) = m ↝f v ▹ (m ↝f* vs)


module SigMorCat where
  module Id-mor (Σ : Signature) where
    open FormalTerm Σ

    id-π : (ar : Arity Σ) → HVec (ar ⊩_) ar
    id-π [] = ⟨⟩
    id-π (s ∷ ar) = (# Fin.zero) ▹ ↑* ar s (id-π ar)

    id-mor : Σ ↝ Σ
    id-mor = record { ↝ₛ = id
                    ; ↝ₒ = λ {ar} {s} f → f ∣$∣ subst (λ ar' → HVec (ar' ⊩_) ar ) (sym (LP.map-id ar)) (id-π ar)
                    }

  module ∘-mor (Σ₁ Σ₂ Σ₃ : Signature) where
    open FormalTerm
    open _↝_
    open SigMorTerms {Σ₂} {Σ₃} hiding (_⊩₂_)
    _⊩₂_ : Arity Σ₂ → sorts Σ₂ → Set
    _⊩₂_ = _⊩_ Σ₂
    _⊩₃_ : Arity Σ₃ → sorts Σ₃ → Set
    _⊩₃_ = _⊩_ Σ₃
    ∘↝∘  : ∀ {ar} {s} (m : Σ₁ ↝ Σ₂)  (m' : Σ₂ ↝ Σ₃)  → (lmap (↝ₛ m) ar) ⊩₂ (↝ₛ m s) → (lmap (↝ₛ m' ∘ ↝ₛ m) ar) ⊩₃ (↝ₛ m' (↝ₛ m s))
    ∘↝∘ {ar} {s} m m' ft = subst (_⊩₃ (↝ₛ m' (↝ₛ m s))) (sym (LP.map-compose {g = ↝ₛ m'} {↝ₛ m} ar)) (m' ↝f ft)

    _∘↝_ : (m : Σ₁ ↝ Σ₂) (m' : Σ₂ ↝ Σ₃) → Σ₁ ↝ Σ₃
    m ∘↝ m' = record { ↝ₛ = ↝ₛ m' ∘ ↝ₛ m
                     ; ↝ₒ = λ {ar} {s} f → ∘↝∘ m m' (↝ₒ m f)
                     }

{- Reduct algebras -}
module ReductAlgebra {Σₛ Σₜ} (t : Σₛ ↝ Σₜ) where

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
  〈 A 〉 = record { _⟦_⟧ₛ = A ⟨_⟩ₛ ; _⟦_⟧ₒ = A ⟨_⟩ₒ }


{- Reduct homomorphism -}
module ReductHomo {Σₛ Σₜ}  {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
                 (t : Σₛ ↝ Σₜ)
                 (A : Algebra {ℓ₁} {ℓ₂} Σₜ)
                 (A' : Algebra {ℓ₃} {ℓ₄} Σₜ) where

  open Hom
  open Homo
  open FormalTerm Σₜ
  open ReductAlgebra t
  open _↝_

  hcond↝ : ∀ {l₀ l₁ l₂ l₃}
             {A : Algebra {l₀} {l₁} Σₜ}
             {A' : Algebra {l₂} {l₃} Σₜ}
             (h : Homo A A') →
             homCond 〈 A 〉 〈 A' 〉 (′ h ′ ∘ ↝ₛ t)
  hcond↝  {A = A} {A'} h {ar} {s} f as =
                       subst (λ vec → Setoid._≈_ (A' ⟦ ↝ₛ t s ⟧ₛ)
                                    (′ h ′ (↝ₛ t s) ⟨$⟩
                                           ⟦_⟧⊩ A (↝ₒ t f) (reindex (↝ₛ t) as))
                                    (⟦_⟧⊩ A' (↝ₒ t f) vec)
                                    )
                       (mapReindex (↝ₛ t)
                                   (_⟨$⟩_ ∘ ′ h ′)  as)
                       (homCond↝' (lmap (↝ₛ t) ar) (↝ₛ t s) (↝ₒ t f)
                                  (reindex (↝ₛ t) as))

    where
    open FormalTermInt
    homCond↝' : (ar' : Arity Σₜ) → (s' : sorts Σₜ) → (e : ar' ⊩ s') →
                (vs : A ∥ ar' ∥* ) →
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
      where
      homCond↝'vec : (ar₁ : Arity Σₜ) →
                      (es : HVec (_⊩_ ar) ar₁) →
                        _∼v_ {R = (Setoid._≈_ ∘ (A' ⟦_⟧ₛ)) $- }
                          (map (λ x → _⟨$⟩_ (′ h ′ x)) (⟦_⟧⊩* A es vs))
                          (⟦_⟧⊩* A' es (map (λ x → _⟨$⟩_ (′ h ′ x)) vs))
      homCond↝'vec .[] ⟨⟩ = ∼⟨⟩
      homCond↝'vec (s₁ ∷ ar₁) (e ▹ es) = ∼▹ (homCond↝' ar s₁ e vs)
                                                        (homCond↝'vec ar₁ es)
  〈_〉ₕ : Homo A A' → Homo 〈 A 〉 〈 A' 〉
  〈 h 〉ₕ = record  { ′_′ = ′ h ′ ∘ ↝ₛ t
                   ; cond = hcond↝ h
                   }



{- Signature morphisms and Equational logic -}
open _↝_

Img⁻¹ : ∀ {A B : Set} → (f : A → B) → (b : B) → Set
Img⁻¹ {A} f b = Σ[ a ∈ A ] (f a ≡ b)


module TermTrans {Σₛ Σₜ : Signature} (Σ↝ : Σₛ ↝ Σₜ) where
  -- Variable translation
  _↝̬ : Vars Σₛ → Vars Σₜ
  (X ↝̬) s' = Σ[ p ∈ Img⁻¹ (↝ₛ Σ↝) s' ] X (proj₁ p)

  open Hom
  open ReductAlgebra Σ↝
  module TΣₛ = T.OpenTerm Σₛ renaming (T_〔_〕 to TΣₛ〔_〕)
  module TΣₜ = T.OpenTerm Σₜ renaming (T_〔_〕 to TΣₜ〔_〕)

  open TΣₛ 
  open TΣₜ hiding (Env)
  term↝ : (Xₛ : Vars Σₛ) → Homo (TΣₛ〔 Xₛ 〕) (〈 TΣₜ〔 Xₛ ↝̬ 〕 〉)
  term↝ Xₛ = TΣXHom
    where θv : TΣₛ.Env Xₛ 〈 TΣₜ〔 Xₛ ↝̬ 〕 〉
          θv {s} v = TΣₜ.var (Xₛ ↝̬) ((s , refl) , v)
          open TΣₛ.Eval Xₛ (〈 TΣₜ〔 Xₛ ↝̬ 〕 〉) θv

  -- Environment translation: We have a bijection
  〈_〉ₑ : ∀ {ℓ₁ ℓ₂} {Aₜ : Algebra {ℓ₁} {ℓ₂} Σₜ} {Xₛ : Vars Σₛ} →
          (θ : TΣₜ.Env (Xₛ ↝̬) Aₜ) → Env Xₛ 〈 Aₜ 〉
  〈 θ 〉ₑ {s} = λ v → θ ((s , refl) , v)

  _↝ₑ : ∀ {ℓ₁ ℓ₂} {Aₜ : Algebra {ℓ₁} {ℓ₂} Σₜ} {Xₛ : Vars Σₛ} →
          (θ : Env Xₛ 〈 Aₜ 〉) → TΣₜ.Env (Xₛ ↝̬) Aₜ
  _↝ₑ {Aₜ = Aₜ} {Xₛ} θ {s} ((s' , eq) , v) = subst (λ s₀ → Aₜ ∥ s₀ ∥) eq (θ v)


{- Theory translation and preservation of models -}
module TheoryTrans {Σₛ Σₜ : Signature} (Σ↝ : Σₛ ↝ Σₜ)
                   (Xₛ : Vars Σₛ) where

  open TermTrans Σ↝
  open ReductAlgebra Σ↝
  open Hom
  open Setoid
  open TΣₛ
  open TΣₜ hiding (Env)
  private Xₜ : Vars Σₜ
  Xₜ = Xₛ ↝̬

  private _∼ : (s : sorts Σₛ) → sorts Σₜ
  s ∼ = ↝ₛ Σ↝ s

  open Homo
  private _∼ₜ : ∀ {s} → TΣₛ〔 Xₛ 〕 ∥ s ∥ → TΣₜ〔 Xₛ ↝̬ 〕 ∥ s ∼ ∥
  _∼ₜ {s} t = ′ term↝ Xₛ ′ s ⟨$⟩ t

  module ReductTheorem {ℓ₁ ℓ₂}
                       (Aₜ : Algebra {ℓ₁} {ℓ₂} Σₜ)
                       (θ : TΣₜ.Env (Xₛ ↝̬) Aₜ) where

    open TΣₜ.Eval (Xₛ ↝̬) Aₜ θ renaming (⟦_⟧ to ⟦_⟧Σₜ ; TΣXHom to ∣H∣ₜ)
    open TΣₛ.Eval Xₛ 〈 Aₜ 〉 (〈_〉ₑ {Aₜ = Aₜ} θ)
      renaming (⟦_⟧ to ⟦_⟧Σₛ ; TΣXHom to ∣H∣ₛ)
    open TΣₛ.EvalUMP Xₛ 〈 Aₜ 〉 (〈_〉ₑ {Aₜ = Aₜ} θ)
      renaming (extends to extendsₛ;UMP to UMPΣₛ)
    open Homo
    open ReductHomo Σ↝ (TΣₜ〔 Xₛ ↝̬ 〕) Aₜ
    open HomComp

    reductTh : ∀ {s} → (t : TΣₛ〔 Xₛ 〕 ∥ s ∥) →
                 _≈_ (〈 Aₜ 〉 ⟦ s ⟧ₛ) ⟦ t ⟧Σₛ ⟦ t ∼ₜ ⟧Σₜ
    reductTh {s} t = UMPΣₛ ∣H∣ₛ (〈 ∣H∣ₜ 〉ₕ ∘ₕ term↝ Xₛ) he₁ he₂ s t
      where
      he₂ : extendsₛ (〈 ∣H∣ₜ 〉ₕ ∘ₕ term↝ Xₛ)
      he₂ {s} x = Setoid.refl (Aₜ ⟦ s ∼ ⟧ₛ)
      he₁ : extendsₛ ∣H∣ₛ
      he₁ {s} x = Setoid.refl (Aₜ ⟦ s ∼ ⟧ₛ)

  open Eq
  _⊨ₜ_ = _⊨_ Σₜ
  _⊢ₜ_ = _⊢_ Σₜ
  _⊨ₜT_ = _⊨T_ Σₜ
  _⊨ₛT_ = _⊨T_ Σₛ {X = Xₛ}
  _⊨ₛ_ = _⊨_ Σₛ {X = Xₛ}
  -- Equation translation
  eq↝ : ∀ {s} → Equation Σₛ Xₛ s → Equation Σₜ Xₜ (↝ₛ Σ↝ s)
  eq↝ {s} (⋀ t ≈ t' if「 carty 」 cond) =
           ⋀ t ∼ₜ ≈ t' ∼ₜ
                     if「 lmap (↝ₛ Σ↝) carty 」 pmap fcond fcond cond
    where fcond : _
          fcond = (reindex (↝ₛ Σ↝) ∘ map (_⟨$⟩_ ∘ ′ term↝ Xₛ ′))


  module SatProp {ℓ₁ ℓ₂} (Aₜ : Algebra {ℓ₁} {ℓ₂} Σₜ) where


    -- This theorem is usually called "satisfaction property" and
    -- "satisfaction condition" in the handbook (Definition 6.1)
    satProp : ∀ {s} → (e : Equation Σₛ Xₛ s) → Aₜ ⊨ₜ (eq↝ e) → 〈 Aₜ 〉 ⊨ₛ e
    satProp {s} (⋀ t ≈ t' if「 ar 」 (us , us')) sat θ us≈us' = begin
                     ⟦ t ⟧Σₛ      ≈⟨ reductTh t ⟩
                     ⟦ t ∼ₜ ⟧Σₜ    ≈⟨ sat θₜ (∼v-reindex _∼ (reductTh* us≈us')) ⟩
                     ⟦ t' ∼ₜ ⟧Σₜ   ≈⟨ Setoid.sym (〈 Aₜ 〉 ⟦ s ⟧ₛ) (reductTh t') ⟩
                     ⟦ t' ⟧Σₛ     ∎
      where
      open TΣₛ.Eval Xₛ 〈 Aₜ 〉 θ renaming(⟦_⟧ to ⟦_⟧Σₛ ; TΣXHom to ∣H∣ₛ)
      open TΣₛ.EvalUMP Xₛ 〈 Aₜ 〉 θ renaming (UMP to UMPΣₛ ;extends to extendsₛ)
      θₜ : TΣₜ.Env Xₜ Aₜ
      θₜ = _↝ₑ {Aₜ = Aₜ} θ
      open TΣₜ.Eval (Xₛ ↝̬) Aₜ θₜ renaming (⟦_⟧ to ⟦_⟧Σₜ ; TΣXHom to ∣H∣ₜ)
      open ReductTheorem Aₜ θₜ
      reductTh* : ∀ {ar₀}
                  {us₀ us₀' : HVec (λ s' →  TΣₛ〔 Xₛ 〕 ∥ s' ∥) ar₀} →
                  _∼v_ {R = λ {sᵢ} uᵢ uᵢ' → _≈_ (〈 Aₜ 〉 ⟦ sᵢ ⟧ₛ) ⟦ uᵢ ⟧Σₛ ⟦ uᵢ' ⟧Σₛ} us₀ us₀' →
                  _∼v_ {R = λ {sᵢ} uᵢ∼ uᵢ∼' → _≈_ (Aₜ ⟦ sᵢ ∼ ⟧ₛ) ⟦ uᵢ∼ ⟧Σₜ ⟦ uᵢ∼' ⟧Σₜ}
                       (map (λ s₀ → _∼ₜ {s₀}) us₀)
                       (map (λ s₀ → _∼ₜ {s₀}) us₀')
      reductTh* {[]} ∼⟨⟩ = ∼⟨⟩
      reductTh* {s₀ ∷ _} (∼▹ {t₁ = u₀} {u₀'} eq eqs) = ∼▹ u₀≈u₀' (reductTh* eqs)
        where
        u₀≈u₀' = begin
           ⟦ u₀ ∼ₜ ⟧Σₜ   ≈⟨ Setoid.sym (Aₜ ⟦ s₀ ∼ ⟧ₛ) (reductTh u₀) ⟩
           ⟦ u₀ ⟧Σₛ     ≈⟨ eq ⟩
           ⟦ u₀' ⟧Σₛ    ≈⟨ reductTh u₀' ⟩
           ⟦ u₀' ∼ₜ ⟧Σₜ ∎
           where open EqR (Aₜ ⟦ s₀ ∼ ⟧ₛ)
      open EqR (〈 Aₜ 〉 ⟦ s ⟧ₛ)

  -- Translation of theories
  _↝T : ∀ {ar} → (Thₛ : Theory Σₛ Xₛ ar) → Theory Σₜ Xₜ (lmap (↝ₛ Σ↝) ar)
  Thₛ ↝T = reindex _∼ (map (λ s → eq↝ {s}) Thₛ)

  ∈↝T : ∀ {ar} {s} {e : Equation Σₛ Xₛ s} → (Thₛ : Theory Σₛ Xₛ ar) →
                    e ∈ Thₛ → (eq↝ e) ∈ (Thₛ ↝T)
  ∈↝T {[]} ⟨⟩ ()
  ∈↝T {s ∷ ar} (e ▹ Thₛ) here = here
  ∈↝T {s₀ ∷ ar} (e ▹ Thₛ) (there e∈Thₛ) = there (∈↝T Thₛ e∈Thₛ)

  -- Implication of theories
  _⇒T~_ : ∀ {ar ar'} → Theory Σₜ Xₜ ar → Theory Σₛ Xₛ ar' → Set
  Tₜ ⇒T~ Tₛ = ∀ {s} {ax : Equation Σₛ Xₛ s} → ax ∈ Tₛ → Tₜ ⊢ₜ eq↝ ax



  module ModelPreserv {ar} (Thₛ : Theory Σₛ Xₛ ar) where

    -- Model preservation from a translated theory
    ⊨T↝ : ∀ {ℓ₁ ℓ₂} → (Aₜ : Algebra {ℓ₁} {ℓ₂} Σₜ) → Aₜ ⊨ₜT (Thₛ ↝T) → 〈 Aₜ 〉 ⊨ₛT Thₛ
    ⊨T↝ Aₜ sat {s} {e} = λ ax θ ceq → satProp e (sat (∈↝T Thₛ ax)) θ ceq
      where open SatProp Aₜ

    -- Model preservation from a implicated theory
    ⊨T⇒↝ : ∀ {ℓ₁ ℓ₂} {ar'} →
             (Thₜ : Theory Σₜ Xₜ ar') → (p⇒ : Thₜ ⇒T~ Thₛ) →
             (Aₜ : Algebra {ℓ₁} {ℓ₂} Σₜ) → Aₜ ⊨ₜT Thₜ → 〈 Aₜ 〉 ⊨ₛT Thₛ
    ⊨T⇒↝ Thₜ p⇒ Aₜ A⊨Th {s} {e} ax θ ceq =
      satProp e (soundness (p⇒ ax) Aₜ A⊨Th) θ ceq
      where
      open SatProp Aₜ
      open Soundness-Completeness Σₜ

