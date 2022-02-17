-- Universal Algebra Library
--
-- Proofs of the three isomorphism theorems.
--
module IsoTheorems where

open import Data.List hiding (map)
open import Data.Product hiding (map)
open import Function as F hiding (Surjective;Bijective;_⟶_)
open import Function.Equality as FE renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Function.Bijection renaming (_∘_ to _∘b_)
open import Function.Surjection hiding (_∘_)
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as EqR
open import Relation.Binary.PropositionalEquality as PE
  hiding (refl;sym;trans)
open import Relation.Unary hiding (_⊆_;_⇒_)


open import UnivAlgebra
open import Morphisms
open import HeterogeneousVec
open import Setoids

open Signature
open Hom
open Homo

{- Isomorphism Theorems -}
module FirstIsoTheo {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Σ : Signature}
                     (A : Algebra {ℓ₁} {ℓ₂} Σ)
                     (B : Algebra {ℓ₃} {ℓ₄} Σ)
                     (h : Homo A B) where

 firstIsoTheo : isEpi h → Isomorphism (A / Kernel h) B
 firstIsoTheo epi = record
   { hom = homo
   ; bij = bij
   }
  where
  homo : Homo (A / Kernel h) B
  homo = ker-embedding A B h
  open Surjective
  surj : isEpi homo
  surj s = record
    { from = record
      { _⟨$⟩_ = from (epi s) ⟨$⟩_
      ; cong = Π.cong (′ h ′ s ∘ₛ from (epi s))
      }
    ; right-inverse-of = right-inverse-of (epi s)
    }
  bij : (s : sorts Σ) → Bijective (′ homo ′ s)
  bij s = record
    { injective = F.id
    ; surjective = surj s
    }

open Congruence
open Setoid

module SecondIsoTheo {ℓ₁ ℓ₂ ℓ₃} {Σ : Signature}
                    (A : Algebra {ℓ₁} {ℓ₂} Σ)
                    (Φ Ψ : Congruence {ℓ₃} A)
                    (Ψ⊆Φ : Ψ ⊆ Φ )
                    where

  open IsEquivalence
  -- Φ/Ψ is a congruence on A/Ψ
  Φ/Ψ : Congruence (A / Ψ)
  Φ/Ψ = record
    { rel = rel Φ
    ; welldef = λ { s {a , b} {c , d} (a~c , b~d) a~b →
           trans (cequiv Φ s) (sym (cequiv Φ s) (Ψ⊆Φ s a~c))
          (trans (cequiv Φ s) a~b ((Ψ⊆Φ s b~d))) }
    ; cequiv = λ s → cequiv Φ s
    ; csubst = csubst Φ
    }

  -- A/Φ is isomorphic to (A/Ψ)/(Φ/Ψ)
  secondIsoTheo : Isomorphism (A / Φ) ((A / Ψ) / Φ/Ψ)
  secondIsoTheo = record
    { hom = record
      { ′_′ = λ s → FE.id
      ; cond = condₕ
      }
      ; bij = λ s → record
        { injective = F.id
        ; surjective = record
          { from = FE.id
          ; right-inverse-of = λ x → refl (cequiv Φ s) {x}
          }
        }
    }
    where
    condₕ : homCond (A / Φ) ((A / Ψ) / Φ/Ψ) (λ s → FE.id)
    condₕ {ar} {s} f as = subst ((rel Φ {s}) (A ⟦ f ⟧ₒ ⟨$⟩ as))
                          (PE.cong (_⟨$⟩_ (A ⟦ f ⟧ₒ)) (PE.sym (map-id as)))
                          (refl (cequiv Φ s))

open SetoidPredicate

module ThirdIsoTheo {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Σ : Signature}
                     (A : Algebra {ℓ₁} {ℓ₂} Σ)
                     (B : SubAlg {ℓ₃} A)
                     (Φ : Congruence {ℓ₄} A) where

  module Φ-Eq s = IsEquivalence (cequiv Φ s)

  -- Trace of a congruence in a subalgebra.
  trace : (s : sorts Σ) → Rel ∥ (SubAlgebra B) ⟦ s ⟧ₛ ∥ _
  trace s (b , _) (b' , _) = rel Φ {s} b b'

  -- Collection of equivalence classes that intersect B
  A/Φ∩B : (s : sorts Σ) → Pred ∥ (A / Φ) ⟦ s ⟧ₛ ∥ _
  A/Φ∩B s = λ a → Σ[ b ∈ ∥ (SubAlgebra B) ⟦ s ⟧ₛ ∥ ] (rel Φ {s}) a (proj₁ b)

  -- Item 1 of theorem. The trace of Φ in B is a congruence on B.
  theo₁ : Congruence (SubAlgebra B)
  theo₁ = record { rel = trace $-
                 ; welldef = wellDef
                 ; cequiv = cEquiv
                 ; csubst = λ f x → csubst Φ f (fmap∼v F.id x)
                 }
        where wellDef : (s : sorts Σ) → WellDefRel (SubAlgebra B ⟦ s ⟧ₛ) (trace s)
              wellDef s (eq₁ , eq₂) a₁~a₂ = welldef Φ s (eq₁ , eq₂) a₁~a₂
              cEquiv :  (s : sorts Σ) → IsEquivalence (trace s)
              cEquiv s = record
                { refl = λ {x} → Eq.refl {proj₁ x}
                ; sym = Eq.sym
                ; trans = Eq.trans
                }
                where module Eq = Φ-Eq s
  open SubAlg
  isor : (s : sorts Σ) → SetoidPredicate ((A / Φ) ⟦ s ⟧ₛ)
  isor s = record
    { predicate = A/Φ∩B s
    ; predWellDef = λ { {x} {y} x~y ((a , pa) , eq) → (a , pa) ,
                      Eq.trans (Eq.sym x~y) eq }
    }
    where module Eq = Φ-Eq s

  bs : ∀ ar → (vs : HVec (λ z → Carrier ((A / Φ) ⟦ z ⟧ₛ)) ar) →
            (as : vs Relation.Unary.∈ _⇨v_ ((predicate ∘ isor) $-)) →
          HVec (λ i → Σ[ a ∈ (Carrier (A ⟦ i ⟧ₛ)) ] (predicate (pr B i) a)) ar
  bs [] ⟨⟩ ⇨v⟨⟩ = ⟨⟩
  bs (i ∷ is) (v ▹ vs₁) (⇨v▹ ((b , pv) , bv) as₁) = (b , pv) ▹ bs is vs₁ as₁
  bseq :  ∀ {ar}
          (vs : HVec (λ z → Carrier ((A / Φ) ⟦ z ⟧ₛ)) ar) →
          (as : vs Relation.Unary.∈ _⇨v_ ((predicate ∘ isor) $-)) →
          _∼v_ {R = rel Φ} vs (map (λ _ → proj₁) (bs ar vs as))
  bseq {[]} ⟨⟩ ⇨v⟨⟩ = ∼⟨⟩
  bseq {_ ∷ is} (_ ▹ vs) (⇨v▹ pv pvs) = ∼▹ (proj₂ pv) (bseq {is} vs pvs)


-- A/Φ∩B is a subalgebra of A/Φ
  theo₂ : SubAlg (A / Φ)
  theo₂ = record { pr = isor ; opClosed = io }
    where
    io : ∀ {ar s} → (f : ops Σ (ar , s)) →
           (_⇨v_ ((predicate ∘ isor) $-) ⟨→⟩ predicate (isor s)) (_⟨$⟩_ ((A / Φ) ⟦ f ⟧ₒ))
    io {ar} {s} f {vs} as = SubAlgebra B ⟦ f ⟧ₒ ⟨$⟩ bs ar vs as
                            , csubst Φ f (bseq vs as)

  -- A/Φ∩B is isomorphic to B/(the trace of Φ in B)
  theo₃ : Isomorphism (SubAlgebra theo₂) (SubAlgebra B / theo₁)
  theo₃ = record
    { hom = record
      { ′_′ = ⇉
      ; cond = cond⇉
      }
    ; bij = λ s → let module Eq = Φ-Eq s in
      record
      { injective = λ { {a , (b , pb) , a~b}
                              {c , (d , pd) , c~d} x₁ →
                                Eq.trans a~b (Eq.trans x₁ (Eq.sym  c~d)) }
      ; surjective = record
        { from = record
          { _⟨$⟩_ = λ { (a , pa) → a , ((a , pa) , (Eq.refl {a})) }
          ; cong = λ { {a , pa} {b , pb} x → x }
          }
        ; right-inverse-of = λ x → Eq.refl
        }
      }
    }
    where
    ⇉ : SubAlgebra theo₂ ⟿ (SubAlgebra B / theo₁)
    ⇉ s = record
      { _⟨$⟩_ = λ x → proj₁ (proj₂ x)
      ; cong = λ { {a , (b , pb) , a~b}
                   {c , (d , pd) , c~d} x →
                      Eq.trans (Eq.sym a~b) (Eq.trans x c~d)
                 }
      }
      where module Eq = Φ-Eq s

    cond⇉ : homCond (SubAlgebra theo₂) (SubAlgebra B / theo₁) ⇉
    cond⇉* : ∀ {ar} as →
             map (λ _ → proj₁) (bs ar (map (λ _ → proj₁) as) (⇨₂ as))
             ∼v
             map (λ _ → proj₁) (map (( _⟨$⟩_) ∘ ⇉) as)
    cond⇉  f as = csubst Φ f  (cond⇉* as)
    cond⇉* {[]} ⟨⟩ = ∼⟨⟩
    cond⇉* {i ∷ is} (v ▹ as) = ∼▹ Eq.refl (cond⇉* as)
      where module Eq = Φ-Eq i

{- The homomorphic image of H : A → B is isomorphic to A/ker H -}
iso-A/kerH : ∀ {Σ} {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (A : Algebra {ℓ₁} {ℓ₂} Σ) →
             (B : Algebra {ℓ₃} {ℓ₄} Σ) → (h : Homo A B) →
             (A / Kernel h) ≅ homImg A h
iso-A/kerH {Σ} A B h = record { iso = iso-F }
  where
  i : ∀ s → _ ⟶ _
  i s = record
    { _⟨$⟩_ = λ x → ′ h ′ s ⟨$⟩ x , x , refl (B ⟦ s ⟧ₛ)
    ; cong = F.id
    }
  j : ∀ s → _ ⟶ _
  j s = record
    { _⟨$⟩_ = proj₁ ∘ proj₂
    ; cong = λ { {a , u , eq} {b , v , eq'} a≈b →
      begin
      ′ h ′ s ⟨$⟩ u   ≈⟨ eq ⟩
      a              ≈⟨ a≈b ⟩
      b              ≈⟨ Setoid.sym (B ⟦ s ⟧ₛ) eq' ⟩
      ′ h ′ s ⟨$⟩ v   ∎
      }
    }
    where open EqR (B ⟦ s ⟧ₛ)

  i-cond : homCond (A / Kernel h) (homImg A h) i
  i-cond {ar} {s} f as =
    begin
      ′ h ′ s ⟨$⟩ (A ⟦ f ⟧ₒ ⟨$⟩ as)
        ≈⟨ cond h f as ⟩
      B ⟦ f ⟧ₒ ⟨$⟩ map (λ s' a → ′ h ′ s' ⟨$⟩ a) as
        ≈⟨ Π.cong (B ⟦ f ⟧ₒ) (eq-as as) ⟩
      B ⟦ f ⟧ₒ ⟨$⟩ map (λ _ → proj₁) (map (λ s' → i s' ⟨$⟩_) as)
    ∎
    where
    open EqR (B ⟦ s ⟧ₛ)
    eq-as : ∀ {ar : List (sorts Σ)} (as : HVec (λ s' → ∥ A ⟦ s' ⟧ₛ ∥) ar) →
      _≈_ ((B ⟦_⟧ₛ) ✳ ar)
        (map (λ s' a → ′ h ′ s' ⟨$⟩ a) as)
        (map (λ _ → proj₁) (map (λ s' → i s' ⟨$⟩_) as))
    eq-as {[]} ⟨⟩ = ∼⟨⟩
    eq-as {s' ∷ _} (v ▹ as') = ∼▹ (Setoid.refl (B ⟦ s' ⟧ₛ)) (eq-as as')

  F : Homo (A / Kernel h) (homImg A h)
  F = record
    { ′_′ = i
    ; cond = i-cond
    }
  iso-F : Isomorphism (A / Kernel h) (homImg A h)
  iso-F = record
    { hom = F
    ; bij = λ s → record
      { injective = F.id
      ; surjective = record
        { from = j s
        ; right-inverse-of = proj₂ ∘ proj₂
        }
      }
    }
