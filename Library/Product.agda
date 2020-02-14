{- Product algebra -}
module Product where
open import Relation.Binary
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Product renaming (map to pmap)
open import Function as F
open import Function.Equality as FE renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Relation.Binary.PropositionalEquality as PE hiding ( Reveal_·_is_;[_];isEquivalence)

import Relation.Binary.Reasoning.Setoid as EqR
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)

open import HeterogeneousVec
open import UnivAlgebra hiding (_↦_)


module ProdAlg {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
        {Σ : Signature}
       (A : Algebra {ℓ₁} {ℓ₂} Σ) 
       (B : Algebra {ℓ₃} {ℓ₄} Σ) where

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
  
  open Setoid
  open import Setoids

  Π-std : (s : sorts Σ) → _
  Π-std s = Π-setoid
    where open IndexedSetoid {I = I} (λ i → A i ⟦ s ⟧ₛ)

  private
    _≈*_ : {ar : Arity Σ} → _
    _≈*_ {ar} = _≈_ (Π-std ✳ ar)

  {- Product of algebras -}
  Πalg : Algebra {ℓ₁ ⊔ ℓ₂} {ℓ₁ ⊔ ℓ₃} Σ
  Πalg = record {
            _⟦_⟧ₛ = Π-std
          ; _⟦_⟧ₒ = λ {ar} {s} f → record { _⟨$⟩_ = if f ; cong = cng f}
          }
    where if : ∀ {ar s} (f : ops Σ (ar , s)) → _ → _
          if {ar} {s} f vs i = A i ⟦ f ⟧ₒ ⟨$⟩ map (λ s' x → x i) vs
          cng : ∀ {ar s} (f : ops Σ (ar , s)) → {vs vs' : ∥ Π-std ✳ ar ∥} 
              → vs ≈* vs' → _≈_ (Π-std s) (if f vs) (if f vs')
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


module BinaryProduct {ℓ₁ ℓ₂}
        {Σ : Signature}
       (A : Algebra {ℓ₁} {ℓ₂} Σ) 
       (B : Algebra {ℓ₁} {ℓ₂} Σ) where

       open import Data.Bool
       open ProdAlg {Σ = Σ} A B renaming (_×-alg_ to A×B)
       Ai : Bool → Algebra {ℓ₁} {ℓ₂} Σ
       Ai false = B
       Ai true = A
       open IndexedProduct {Σ = Σ} {Bool} Ai
       open import Morphisms
       open Isomorphism
       open import Function.Injection
       iso×-2→ : Isomorphism A×B Πalg
       iso×-2→ = record { hom = H
                        ; bij = λ s → record {
                            injective = λ x → x true , x false
                          ; surjective = record {
                              from = h⁻¹ s
                            ; right-inverse-of = inv s
                            }
                          }
                        }
               where _$h_ : ∀ {s} → (x : Setoid.Carrier (A×B ⟦ s ⟧ₛ)) → (i : Bool) →
                                    Setoid.Carrier (Ai i ⟦ s ⟧ₛ)
                     p $h false = proj₂ p
                     p $h true = proj₁ p
                     congh : ∀ {s} → {p q : Setoid.Carrier (A×B ⟦ s ⟧ₛ)} →
                            (Setoid._≈_ (A×B ⟦ s ⟧ₛ) p q) → 
                           (i : Bool) → Setoid._≈_ (Ai i ⟦ s ⟧ₛ)  (p $h i) (q $h i)
                     congh eq false = proj₂ eq
                     congh eq true = proj₁ eq
                     condh : Hom.homCond A×B Πalg (λ s → record { _⟨$⟩_ = _$h_ ; cong = λ {i} {j} → congh })
                     condh {ar = ar} f as false
                       rewrite propMapV∘ as (λ x → _$h_)  (λ _ x → x false) = Π.cong (B ⟦ f ⟧ₒ) (Setoid.refl (_⟦_⟧ₛ B ✳ ar))
                     condh {ar = ar} f as true 
                       rewrite propMapV∘ as (λ x → _$h_)  (λ _ x → x true) = Π.cong (A ⟦ f ⟧ₒ) (Setoid.refl (_⟦_⟧ₛ A ✳ ar))

                     H : Hom.Homo A×B Πalg
                     H = record { ′_′ = λ s → record { _⟨$⟩_ = _$h_ {s}
                                                     ; cong = congh {s}
                                                     }
                                ; cond = condh
                                }
                     h⁻¹ : ∀ s → (Πalg ⟦ s ⟧ₛ) ⟶ (A×B ⟦ s ⟧ₛ)
                     h⁻¹ s = record { _⟨$⟩_ = λ t → t true , t false
                                    ; cong = λ x → x true , x false
                                    }
                     
                     inv : ∀ s → (x : (i : Bool) → Setoid.Carrier (Ai i ⟦ s ⟧ₛ)) →
                          (i : Bool) → Setoid._≈_ (Ai i ⟦ s ⟧ₛ)  ((x true , x false) $h i) (x i)
                     inv s f false = Setoid.refl (B ⟦ s ⟧ₛ)
                     inv s f true = Setoid.refl (A ⟦ s ⟧ₛ)
