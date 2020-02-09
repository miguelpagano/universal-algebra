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
          cng {ar} f equ = Π.cong (_⟦_⟧ₒ A f) (fmap∼v proj₁ equ) ,
                           Π.cong (_⟦_⟧ₒ B f) (fmap∼v proj₂ equ) 

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



module IndexedProduct {ℓ₁ ℓ₂ ℓ₃}
        {Σ : Signature} {I : Set ℓ₁}
        (A : I → Algebra {ℓ₂} {ℓ₃} Σ) where
      
  open Signature
  open Algebra
  open Setoid
  open import Setoids
  
  std : (s : sorts Σ) → Setoid (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₃)
  std s = record { Carrier = (i : I) → carrier i
                           ; _≈_ = ≈ᵢ
                           ; isEquivalence = isEquiv
                           }
   where carrier : I → Set ℓ₂
         carrier i = Setoid.Carrier (A i ⟦ s ⟧ₛ)
         A-std : _ → _
         A-std i = A i ⟦ s ⟧ₛ
         ≈ᵢ : Rel ((i : I) → (carrier i)) (ℓ₁ ⊔ ℓ₃)
         ≈ᵢ f g = ∀ i → Setoid._≈_ (A-std i) (f i) (g i)
         isEquiv : IsEquivalence ≈ᵢ
         isEquiv = record { refl = λ i → Setoid.refl (A-std i)
                          ; sym = λ x i → Setoid.sym (A-std i) (x i)
                          ; trans = λ x x₁ i → Setoid.trans (A-std i) (x i) (x₁ i)
                          }
  

  _≈*_ : {ar : Arity Σ} → _
  _≈*_ {ar} = _≈_ (std ✳ ar)

  {- Product of algebras -}
  Πalg : Algebra {ℓ₁ ⊔ ℓ₂} {ℓ₁ ⊔ ℓ₃} Σ
  Πalg = record {
            _⟦_⟧ₛ = λ s → std s
          ; _⟦_⟧ₒ = λ {ar} {s} f → record { _⟨$⟩_ = if f ; cong = cng f}
          }
    where if : ∀ {ar s} (f : ops Σ (ar , s)) → _ → _
          if {ar} {s} f vs i = A i ⟦ f ⟧ₒ ⟨$⟩ map (λ s' x → x i) vs
          cng : ∀ {ar s} (f : ops Σ (ar , s)) → {vs vs' : ∥ std ✳ ar ∥} 
              → vs ≈* vs' → _≈_ (std s) (if f vs) (if f vs')
          cng {ar} f equ i = Π.cong (A i ⟦ f ⟧ₒ) (fmap∼v (_$ i) equ)

  
  {- Projection homomorphisms -}
  open import Morphisms
  open import Data.Product.Function.NonDependent.Setoid
  open Hom
  open Homo
  π : (i : I) → Homo Πalg (A i)
  π i = record { ′_′ = λ _ → record { _⟨$⟩_ = _$ i ; cong = _$ i } ;
               cond = λ {_} {s} f as → Setoid.refl (A i ⟦ s ⟧ₛ)
               }

  module PairMor {ℓ} {ℓ'} (C : Algebra {ℓ} {ℓ'} Σ)  where
    ⟨_⟩ : (f : (i : I) → Homo C (A i)) → Homo C Πalg
    ⟨ f ⟩ = record { ′_′ = λ s → record { _⟨$⟩_ = λ c i →  ′ f i ′ s ⟨$⟩ c
                                       ; cong = λ c i → Π.cong (′ f i ′ s) c
                                       } 
                   ; cond = hom-cond
                   }
      where _≈Ai_ : ∀ {s : sorts Σ} {i} → _
            _≈Ai_ {s} {i} = _≈_ (A i ⟦ s ⟧ₛ)
            <f> : (s : sorts Σ) → Setoid.Carrier (C ⟦ s ⟧ₛ) → (i : I) → Setoid.Carrier (A i ⟦ s ⟧ₛ) 
            <f> s c j = ′ f j ′ s ⟨$⟩ c
            hom-cond : ∀ {s} {ar} (ft : ops Σ (ar , s)) (cs : HVec _ ar) i →
                      (′ f i ′ s ⟨$⟩ ((C ⟦ ft ⟧ₒ) ⟨$⟩ cs)) ≈Ai
                      (((A i ⟦ ft ⟧ₒ) ⟨$⟩ map (λ _ x → x i) (map <f> cs)))
            hom-cond {s} ft cs i rewrite (propMapV∘ cs <f> (λ s' x → x i)) = cond (f i) ft cs

open import Equational
module IndexedProductModel 
        {Σ : Signature}
        {X : Vars Σ}
        {ar : _}
        {E : Theory Σ X ar}
        {ℓ₁ ℓ₂ ℓ₃}
        {I : Set ℓ₁}
        {A : I → Algebra {ℓ₂} {ℓ₃} Σ}
        (Ai⊨E : (i : I) → A i ⊨T E)
        where

       open Algebra
       open Signature
       open IndexedProduct {I = I} A 
       import Setoids using (∥_∥)
       open import TermAlgebra (Σ 〔 X 〕)
       open HU

       module Aux (θ : Env X Πalg) where
           open EnvExt X Πalg renaming (_↪ to _↪×;map↪ to map↪×)
           θi : (i : I) → Env X (A i)
           θi i x = (θ x) i
           open import Morphisms
           module E i = EnvExt X (A i) renaming (_↪ to _↪A) hiding (map↪)
           module HA i = Hom T Σ 〔 X 〕 (A i)
           module IA i = InitHomoExt (A i) (θi i) renaming (TΣXHom to TΣXHomAi)
           open IA 
           open E public
           open HA
           open InitHomoExt
           open HomComp
           
           HA : (i : I) → HA.Homo i
           HA i = π i ∘ₕ TΣXHom Πalg θ
           
           _,_≈a_ : {i : I} → (s : sorts Σ) → _
           _,_≈a_ {i} s = Setoid._≈_ (A i ⟦ s ⟧ₛ)
           
           HA≈I : ∀ {s} → (i : I) → (t : HU s)  →  s , _↪A i (θi i) t ≈a ((_$ i) ∘ (θ ↪×)) t
           HA≈I {s} i t = IA.tot i (IA.TΣXHomAi i) (HA i) prop prop s t
             where prop : (s : sorts Σ) → (x : X s) → s , θ x i ≈a θ x i  -- s , proj₁ (θ x) ≈ (proj₁ (θ x))
                   prop s x = Setoid.refl (A i ⟦ s ⟧ₛ)

           eqA : ∀ {s} {t t' : HU s} i → s , _↪A i (θi i) t ≈a (_↪A i) (θi i) t' → s , ((_$ i) ∘ (θ ↪×)) t ≈a ((_$ i) ∘ (θ ↪×)) t'
           eqA {s} {t} {t'} i eq = begin
                                ((_$ i) ∘ (θ ↪×)) t
                                ≈⟨ Setoid.sym (A i ⟦ s ⟧ₛ) (HA≈I i t) ⟩
                                (_↪A i) (θi i) t
                                ≈⟨ eq ⟩
                                (_↪A i) (θi i) t'
                                ≈⟨  HA≈I i t' ⟩
                                ((_$ i) ∘ (θ ↪×)) t'
                                ∎
                where open EqR (A i ⟦ s ⟧ₛ)

           eqA' : ∀ {s} {t t' : HU s} i → s , ((_$ i) ∘ (θ ↪×)) t ≈a ((_$ i) ∘ (θ ↪×)) t' → s , (_↪A i) (θi i) t ≈a  (_↪A i) (θi i) t'
           eqA' {s} {t} {t'} i eq = begin
                                (_↪A i) (θi i) t
                                ≈⟨ HA≈I i t ⟩
                                ((_$ i) ∘ (θ ↪×)) t
                                ≈⟨ eq ⟩
                                ((_$ i) ∘ (θ ↪×)) t'
                                ≈⟨ Setoid.sym (A i ⟦ s ⟧ₛ) (HA≈I i t') ⟩
                                (_↪A i) (θi i) t'
                                ∎
                where open EqR (A i ⟦ s ⟧ₛ)



       Πalg⊨E : Πalg ⊨T E 
       Πalg⊨E {s} {e} e∈E θ eqs i = eqA {s} {left e} {right e} i (Ai⊨E i e∈E (θi i) eqsA)
              where open Aux θ
                    open Equation
                    eqsA : _
                    eqsA = map∼v (λ {s'} {t} {t'} eq → eqA' {s'} {t} {t'} i (eq i)) eqs

