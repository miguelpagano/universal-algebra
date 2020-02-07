{- Product algebra -}
module Product where
open import Relation.Binary hiding (Total)
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Nat renaming (_⊔_ to _⊔ₙ_)
open import Data.Product renaming (map to pmap)
open import Function as F
open import Function.Equality as FE renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Data.Bool renaming (_≟_ to _≟b_)
open import Data.List renaming (map to lmap)
open import Relation.Binary.PropositionalEquality as PE hiding ( Reveal_·_is_;[_];isEquivalence)
open import Relation.Unary hiding (_⊆_;_⇒_)

open import Data.Fin hiding (_+_)

import Relation.Binary.Reasoning.Setoid as EqR
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)

open import HeterogeneousVec
open import UnivAlgebra hiding (_↦_)


module ProdAlg {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
        {Σ : Signature}
       (A : Algebra {ℓ₁} {ℓ₂} Σ) 
       (B : Algebra {ℓ₃} {ℓ₄} Σ) where

  open Signature
  open Algebra
  open Setoid
  open import Setoids
  
  std : (s : sorts Σ) → Setoid _ _
  std s = ×-setoid (A ⟦ s ⟧ₛ) (B ⟦ s ⟧ₛ)
  _≈*_ : {ar : Arity Σ} → _
  _≈*_ {ar} = _≈_ (std ✳ ar)

  ≈₁ : ∀ {s} {a a' : ∥ std s ∥} → Setoid._≈_ (std s) a a' → _≈_ (A ⟦ s ⟧ₛ) (proj₁ a) (proj₁ a')
  ≈₁ (eq , _ ) = eq
  ≈₂ : ∀ {s} {a a' : ∥ std s ∥} → Setoid._≈_ (std s) a a' → _≈_ (B ⟦ s ⟧ₛ) (proj₂ a) (proj₂ a')
  ≈₂ (_ , eq ) = eq

  ≈ᵢ : ∀ {s} {a a' : ∥ std s ∥} → _≈_ (A ⟦ s ⟧ₛ) (proj₁ a) (proj₁ a') → _≈_ (B ⟦ s ⟧ₛ) (proj₂ a) (proj₂ a') →
    Setoid._≈_ (std s) a a'
  ≈ᵢ eq eq' = eq , eq'

  ≈×₁ : ∀ {ar} {vs vs' : ∥ std ✳ ar ∥} 
      → vs ≈* vs' → _≈_ (_⟦_⟧ₛ A ✳ ar) (map (λ _ → proj₁) vs) (map (λ _ → proj₁) vs')
  ≈×₁ {[]} ∼⟨⟩ = ∼⟨⟩
  ≈×₁ {i ∷ is} (∼▹ (eq , _) equ) = ∼▹ eq (≈×₁ equ)
  ≈×₂ : ∀ {ar} {vs vs' : ∥ std ✳ ar ∥} 
      → vs ≈* vs' → _≈_ (_⟦_⟧ₛ B ✳ ar) (map (λ _ → proj₂) vs) (map (λ _ → proj₂) vs')
  ≈×₂ {[]} ∼⟨⟩ = ∼⟨⟩
  ≈×₂ {i ∷ is} (∼▹ (_ , eq) equ) = ∼▹ eq (≈×₂ equ)

  {- Product of algebras -}
  _×-alg_ : Algebra {ℓ₃ ⊔ ℓ₁} {ℓ₄ ⊔ ℓ₂} Σ
  _×-alg_ = record {
            _⟦_⟧ₛ = λ s → ×-setoid (A ⟦ s ⟧ₛ) (B ⟦ s ⟧ₛ)
          ; _⟦_⟧ₒ = λ {ar} {s} f → record { _⟨$⟩_ = if f ; cong = cng f}
          }
    where if : ∀ {ar s} (f : ops Σ (ar , s)) → _ → _
          if {ar} {s} f vs =  A ⟦ f ⟧ₒ ⟨$⟩ map (λ _ → proj₁) vs
                            , B ⟦ f ⟧ₒ ⟨$⟩ map (λ _ → proj₂) vs
          cng : ∀ {ar s} (f : ops Σ (ar , s)) → {vs vs' : ∥ std ✳ ar ∥} 
              → vs ≈* vs' → _≈_ (std s) (if f vs) (if f vs')
          cng {ar} f equ = (Π.cong (_⟦_⟧ₒ A f) (≈×₁ equ)) ,
                           ((Π.cong (_⟦_⟧ₒ B f) (≈×₂ equ)))

  {- Projection homomorphisms -}
  open import Morphisms
  open import Data.Product.Function.NonDependent.Setoid
  open Hom
  open Homo
  π₁ : Homo _×-alg_ A
  π₁ = record { ′_′ = λ _ → proj₁ₛ ; cond = λ {_} {s} f as → Setoid.refl (A ⟦ s ⟧ₛ) }
  
  π₂ : Homo _×-alg_ B
  π₂ = record { ′_′ = λ _ → proj₂ₛ ; cond = λ {_} {s} f as → Setoid.refl (B ⟦ s ⟧ₛ) }

  module PairMor {ℓ} {ℓ'} (C : Algebra {ℓ} {ℓ'} Σ)  where
    ⟨_,_⟩ : (f : Homo C A) → (g : Homo C B) → Homo C _×-alg_
    ⟨ f , g ⟩ = record { ′_′ = λ s → < ′ f ′ s , ′ g ′ s >ₛ 
                     ; cond = λ {_} {s} ft as → hom-cond ft as
                     }
      where _≈×_ : ∀ {s : sorts Σ} → _
            _≈×_ {s} = _≈_ (_×-alg_ ⟦ s ⟧ₛ)
            fg : _
            fg x = < _⟨$⟩_ (′ f ′ x) , _⟨$⟩_ (′ g ′ x) >
            hom-cond : ∀ {s} {ar} (ft : ops Σ (ar , s)) (as : HVec _ ar) →
                     (< ′ f ′ s , ′ g ′ s >ₛ ⟨$⟩ ((C ⟦ ft ⟧ₒ) ⟨$⟩ as)) ≈× 
                                  (_×-alg_ ⟦ ft ⟧ₒ ⟨$⟩ (map (λ x → < _⟨$⟩_ (′ f ′ x) , _⟨$⟩_ (′ g ′ x) >) as))
            hom-cond {s} ft as rewrite propMapV∘ as fg (λ _ → proj₁)
                                     | propMapV∘ as fg (λ _ → proj₂) = cond f ft as , cond g ft as


open import Equational
module ProdModel 
        {Σ : Signature}
        {X : Vars Σ}
        {ar : _}
        {E : Theory Σ X ar}
        {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
        {A : Algebra {ℓ₁} {ℓ₂} Σ}
        {B : Algebra {ℓ₃} {ℓ₄} Σ}
        (A⊨E : A ⊨T E)
        (B⊨E : B ⊨T E) where

       open Algebra
       open Signature
       open ProdAlg A B renaming (_×-alg_ to A×B)
       import Setoids using (∥_∥)
       open import TermAlgebra (Σ 〔 X 〕)
       open HU
       open import Data.Sum hiding (map)

       module Aux (θ : Env X A×B) where
           open EnvExt X A×B renaming (_↪ to _↪×;map↪ to map↪×)
           θa : Env X A
           θa x = proj₁ (θ x)
           θb : Env X B
           θb x = proj₂ (θ x)
           open import Morphisms
           open module EA = EnvExt X A renaming (_↪ to _↪A) public
           open module EB = EnvExt X B renaming (_↪ to _↪B) hiding (map↪) public
           open module HA = Hom T Σ 〔 X 〕 A
           open module HB = Hom T Σ 〔 X 〕 B
           open module IA = InitHomoExt A θa renaming (TΣXHom to TΣXHomA)
           open module IB = InitHomoExt B θb renaming (TΣXHom to TΣXHomB)
           open InitHomoExt
           open HomComp
           
           HA : HA.Homo
           HA = π₁ ∘ₕ TΣXHom A×B θ

           HB : HB.Homo
           HB = π₂ ∘ₕ TΣXHom A×B θ
           
           _,_≈a_ : (s : sorts Σ) → _
           _,_≈a_ s = Setoid._≈_ (A ⟦ s ⟧ₛ)
           _,_≈b_ : (s : sorts Σ) → _
           _,_≈b_ s = Setoid._≈_ (B ⟦ s ⟧ₛ)
           
           HA≈I : ∀ {s} → (t : HU s) → s , (θa ↪A) t ≈a (λ i → proj₁ ((θ ↪×) i)) t
           HA≈I {s} t = IA.tot IA.TΣXHom HA prop prop s t
             where prop : (s : sorts Σ) → (x : X s) → ((A ⟦ s ⟧ₛ) Setoid.≈ proj₁ (θ x)) (proj₁ (θ x))
                   prop s x = Setoid.refl (A ⟦ s ⟧ₛ)

           HB≈I : ∀ {s} → (t : HU s) → s , (θb ↪B) t ≈b (λ i → proj₂ ((θ ↪×) i)) t
           HB≈I {s} t = IB.tot IB.TΣXHom HB prop prop s t
             where prop : (s : sorts Σ) → (x : X s) → ((B ⟦ s ⟧ₛ) Setoid.≈ proj₂ (θ x)) (proj₂ (θ x))
                   prop s x = Setoid.refl (B ⟦ s ⟧ₛ)

           eqA : ∀ {s} {t t' : HU s} → s , (θa ↪A) t ≈a  (θa ↪A) t' → s , (proj₁ ∘ (θ ↪×)) t ≈a (proj₁ ∘ (θ ↪×)) t'
           eqA {s} {t} {t'} eq = begin
                                (proj₁ ∘ (θ ↪×)) t
                                ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (HA≈I t) ⟩
                                (θa ↪A) t
                                ≈⟨ eq ⟩
                                (θa ↪A) t'
                                ≈⟨  HA≈I t' ⟩
                                (proj₁ ∘ (θ ↪×)) t'
                                ∎
                where open EqR (A ⟦ s ⟧ₛ)

           eqA' : ∀ {s} {t t' : HU s} → s , (proj₁ ∘ (θ ↪×)) t ≈a (proj₁ ∘ (θ ↪×)) t' → s , (θa ↪A) t ≈a  (θa ↪A) t'
           eqA' {s} {t} {t'} eq = begin
                                (θa ↪A) t
                                ≈⟨ HA≈I t ⟩
                                (proj₁ ∘ (θ ↪×)) t
                                ≈⟨ eq ⟩
                                (proj₁ ∘ (θ ↪×)) t'
                                ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (HA≈I t') ⟩
                                (θa ↪A) t'
                                ∎
                where open EqR (A ⟦ s ⟧ₛ)


           eqB : ∀ {s} {t t' : HU s} → s , (θb ↪B) t ≈b  (θb ↪B) t' → s , (proj₂ ∘ (θ ↪×)) t ≈b (proj₂ ∘ (θ ↪×)) t'
           eqB {s} {t} {t'} eq = begin
                                (proj₂ ∘ (θ ↪×)) t
                                ≈⟨ Setoid.sym (B ⟦ s ⟧ₛ) (HB≈I t) ⟩
                                (θb ↪B) t
                                ≈⟨ eq ⟩
                                (θb ↪B) t'
                                ≈⟨  HB≈I t' ⟩
                                (proj₂ ∘ (θ ↪×)) t'
                                ∎
                where open EqR (B ⟦ s ⟧ₛ)

           eqB' : ∀ {s} {t t' : HU s} → s , (proj₂ ∘ (θ ↪×)) t ≈b (proj₂ ∘ (θ ↪×)) t' → s , (θb ↪B) t ≈b  (θb ↪B) t'
           eqB' {s} {t} {t'} eq = begin
                                (θb ↪B) t
                                ≈⟨ HB≈I t ⟩
                                (proj₂ ∘ (θ ↪×)) t
                                ≈⟨ eq ⟩
                                (proj₂ ∘ (θ ↪×)) t'
                                ≈⟨ Setoid.sym (B ⟦ s ⟧ₛ) (HB≈I t') ⟩
                                (θb ↪B) t'
                                ∎
                where open EqR (B ⟦ s ⟧ₛ)



       A×B⊨E : A×B ⊨T E 
       A×B⊨E {s} {e} e∈E θ eqs = eqA {s} {left e} {right e} (A⊨E e∈E θa eqsA)
                               , eqB {s} {left e} {right e} (B⊨E e∈E θb eqsB)
              where open Aux θ
                    open Equation
                    eqsA : _∼v_ {_} {_} {sorts Σ} {HU}
                            {λ sᵢ uᵢ uᵢ' → ((A ⟦ sᵢ ⟧ₛ) Setoid.≈
                            (θa ↪A) uᵢ)
                            ((θa ↪A) uᵢ')}
                            {carty e} (proj₁ (cond e)) (proj₂ (cond e))
                    eqsA = map∼v (λ { {s'} {t} {t'} (eq , _) → eqA' {s'} {t} {t'} eq}) eqs
                    eqsB : _∼v_ {_} {_} {sorts Σ} {HU}
                            {λ sᵢ uᵢ uᵢ' → ((B ⟦ sᵢ ⟧ₛ) Setoid.≈
                            (θb ↪B) uᵢ)
                            ((θb ↪B) uᵢ')}
                            {carty e} (proj₁ (cond e)) (proj₂ (cond e))
                    eqsB = map∼v (λ { {s'} {t} {t'} (_ , eq) → eqB' {s'} {t} {t'} eq}) eqs
