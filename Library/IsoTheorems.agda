{- Proofs of the three isomorphism theorems -}

module IsoTheorems where

open import UnivAlgebra
open import Morphisms
open import HeterogeneousVec
open import Setoids
open import Function as F hiding (Surjective;Bijective)
open import Function.Equality as FE renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Function.Bijection renaming (_∘_ to _∘b_)
open import Function.Surjection hiding (_∘_)
open import Relation.Binary.PropositionalEquality as PE hiding (refl)
open import Data.Product hiding (map)
open import Relation.Binary
open import Relation.Unary hiding (_⊆_;_⇒_)
open import Data.List hiding (map)

open Signature
open Hom
open Homo

{- Isomorphism Theorems -}
module FirstIsoTheo {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Σ : Signature}
                     (A : Algebra {ℓ₁} {ℓ₂} Σ)
                     (B : Algebra {ℓ₃} {ℓ₄} Σ)
                     (h : Homo A B) where

 firstIsoTheo : (surj : (s : sorts Σ) → Surjective (′ h ′ s)) → Isomorphism (A / Kernel h) B
 firstIsoTheo surj =
             record { hom = homo₁
                    ; bij = bij₁
                    }
  where homo₁ : Homo (A / Kernel h) B
        homo₁ = KerEmbedding A B h
        open Surjective
        surj₁ : (s : sorts Σ) → Surjective (′ homo₁ ′ s)
        surj₁ s = record { from = record { _⟨$⟩_ = from (surj s) ⟨$⟩_
                                         ; cong = Π.cong (′ h ′ s ∘ₛ from (surj s))
                                         }
                         ; right-inverse-of = right-inverse-of (surj s)
                         }
        bij₁ : (s : sorts Σ) → Bijective (′ homo₁ ′ s)
        bij₁ s = record { injective = F.id
                        ; surjective = surj₁ s }


open Congruence
open Setoid
open Algebra

module SecondIsoTheo {ℓ₁ ℓ₂ ℓ₃} {Σ : Signature}
                    (A : Algebra {ℓ₁} {ℓ₂} Σ)
                    (Φ Ψ : Congruence {ℓ₃} A)
                    (Ψ⊆Φ : Ψ ⊆ Φ )
                    where

  open IsEquivalence renaming (trans to tr ; sym to sy ; refl to re)
  -- Φ/Ψ is a congruence on A/Ψ
  theo₁ : Congruence (A / Ψ)
  theo₁ = record { rel = rel Φ
                 ; welldef = λ { s {a , b} {c , d} (a~c , b~d) a~b →
                        tr (cequiv Φ s) (sy (cequiv Φ s) (Ψ⊆Φ s a~c))
                       (tr (cequiv Φ s) a~b ((Ψ⊆Φ s b~d))) }
                 ; cequiv = λ s → cequiv Φ s
                 ; csubst = csubst Φ
                 }


  -- A/Φ is isomorphic to (A/Ψ)/(Φ/Ψ)
  secondIsoTheo : Isomorphism (A / Φ) ((A / Ψ) / theo₁)
  secondIsoTheo =
          record { hom = record { ′_′ = λ s → FE.id ; cond = condₕ }
                 ; bij = λ s → record { injective = F.id
                                      ; surjective = record { from = FE.id
                                        ; right-inverse-of = λ x → re (cequiv Φ s) {x} }
                                      }
                 }
        where
              condₕ : homCond (A / Φ) ((A / Ψ) / theo₁) (λ s → FE.id)
              condₕ {ar} {s} f as = subst ((rel Φ s) (A ⟦ f ⟧ₒ ⟨$⟩ as))
                                    (PE.cong (_⟨$⟩_ (A ⟦ f ⟧ₒ)) (PE.sym (mapId as)))
                                    (IsEquivalence.refl (cequiv Φ s))

open SetoidPredicate

module ThirdIsoTheo {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Σ : Signature}
                     (A : Algebra {ℓ₁} {ℓ₂} Σ)
                     (B : SubAlg {ℓ₃} A)
                     (Φ : Congruence {ℓ₄} A) where

  -- Trace of a congruence in a subalgebra.
  trace : (s : sorts Σ) → Rel ∥ (SubAlgebra B) ⟦ s ⟧ₛ ∥ _
  trace s (b , _) (b' , _) = rel Φ s b b'

  -- Collection of equivalence classes that intersect B
  A/Φ∩B : (s : sorts Σ) → Pred ∥ (A / Φ) ⟦ s ⟧ₛ ∥ _
  A/Φ∩B s = λ a → Σ[ b ∈ ∥ (SubAlgebra B) ⟦ s ⟧ₛ ∥ ] (rel Φ s) a (proj₁ b)

  -- Item 1 of theorem. The trace of Φ in B is a congruence on B.
  theo₁ : Congruence (SubAlgebra B)
  theo₁ = record { rel = trace
                 ; welldef = wellDef
                 ; cequiv = cEquiv
                 ; csubst = λ f x → csubst Φ f (fmap∼v F.id x)
                 }
        where wellDef : (s : sorts Σ) → WellDefRel (SubAlgebra B ⟦ s ⟧ₛ) (trace s)
              wellDef s (eq₁ , eq₂) a₁~a₂ = welldef Φ s (eq₁ , eq₂) a₁~a₂
              cEquiv :  (s : sorts Σ) → IsEquivalence (trace s)
              cEquiv s = record { refl = λ {x} → IsEquivalence.refl (cequiv Φ s) {proj₁ x}
                                ; sym = IsEquivalence.sym (cequiv Φ s)
                                ; trans = IsEquivalence.trans (cequiv Φ s)
                                }
  open SubAlg
  isor : (s : sorts Σ) → SetoidPredicate ((A / Φ) ⟦ s ⟧ₛ)
  isor s = record { predicate = A/Φ∩B s
                  ; predWellDef = λ { {x} {y} x~y ((a , pa) , eq) → (a , pa) ,
                                          tr (sy x~y) eq }
                  }
                where open IsEquivalence (cequiv Φ s) renaming (trans to tr ; sym to sy)

  bs : ∀ ar → (vs : HVec (λ z → Carrier ((A / Φ) ⟦ z ⟧ₛ)) ar) →
            (as : vs Relation.Unary.∈ _⇨v_ ((predicate) ∘ isor)) →
          HVec (λ i → Σ[ a ∈ (Carrier (A ⟦ i ⟧ₛ)) ] (predicate (pr B i) a)) ar
  bs [] ⟨⟩ ⇨v⟨⟩ = ⟨⟩
  bs (i ∷ is) (v ▹ vs₁) (⇨v▹ ((b , pv) , bv) as₁) = (b , pv) ▹ bs is vs₁ as₁
     where open IsEquivalence (cequiv Φ i) renaming (trans to tr ; sym to sy)
  bseq :  ∀ {ar}
          (vs : HVec (λ z → Carrier ((A / Φ) ⟦ z ⟧ₛ)) ar) →
          (as : vs Relation.Unary.∈ _⇨v_ ((predicate) ∘ isor)) →
          _∼v_ {R = rel Φ} vs (map (λ _ → proj₁) (bs ar vs as))
  bseq {[]} ⟨⟩ ⇨v⟨⟩ = ∼⟨⟩
  bseq {i ∷ is} (v ▹ vs) (⇨v▹ pv as₁) = ∼▹ (proj₂ pv)
                                                  (bseq {is} vs as₁)


-- A/Φ∩B is a subalgebra of A/Φ
  theo₂ : SubAlg (A / Φ)
  theo₂ = record { pr = isor ; opClosed = io }
          where
            io : ∀ {ar s} → (f : ops Σ (ar , s)) →
              (_⇨v_ (( predicate) ∘ isor) ⟨→⟩ predicate (isor s)) (_⟨$⟩_ ((A / Φ) ⟦ f ⟧ₒ))
            io {ar} {s} f {vs} as = SubAlgebra B ⟦ f ⟧ₒ ⟨$⟩ bs ar vs as
                                  , csubst Φ f (bseq vs as)

  open IsEquivalence  renaming (refl to ref;sym to symm;trans to tran)

  -- A/Φ∩B is isomorphic to B/(the trace of Φ in B)
  theo₃ : Isomorphism (SubAlgebra theo₂) (SubAlgebra B / theo₁)
  theo₃ = record {
        hom = record {
            ′_′ = ⇉
        ; cond = cond⇉ }
      ; bij = λ s → record
            { injective = λ { {a , (b , pb) , a~b}
                              {c , (d , pd) , c~d} x₁ →
                                tran (cequiv Φ s) a~b
                                (tran (cequiv Φ s) x₁
                                  (symm (cequiv Φ s) c~d)) }
            ; surjective = record {
                           from = record { _⟨$⟩_ = λ { (a , pa) → a , ((a , pa) , (ref (cequiv Φ s) {a})) }
                                         ; cong = λ { {a , pa} {b , pb} x → x }}
                         ; right-inverse-of = λ x → ref (cequiv Φ s)
                         }
            }
      }
      where ⇉ : SubAlgebra theo₂ ⟿ (SubAlgebra B / theo₁)
            ⇉ s = record { _⟨$⟩_ = λ x → proj₁ (proj₂ x)
                          ; cong = λ { {a , (b , pb) , a~b}
                                      {c , (d , pd) , c~d} x →
                                            tran (cequiv Φ s) (symm (cequiv Φ s) a~b)
                                            (tran (cequiv Φ s) x c~d)}
                          }
            cond⇉ : homCond (SubAlgebra theo₂) (SubAlgebra B / theo₁) ⇉
            cond⇉* : ∀ {ar} as →  map (λ _ → proj₁) (bs ar (map (λ _ → proj₁) as)
                                                         (⇨₂ as))
                                    ∼v
                                 map (λ _ → proj₁) (map (( _⟨$⟩_) ∘ ⇉) as)
            cond⇉  f as = csubst Φ f  (cond⇉* as)
            cond⇉* {[]} ⟨⟩ = ∼⟨⟩
            cond⇉* {i ∷ is} (v ▹ as) = ∼▹ (ref (cequiv Φ i)) (cond⇉* as)

{- The homomorphic image of H : A → B is isomorphic to A/ker H -}
import Relation.Binary.EqReasoning as EqR
open Setoid
iso-A/kerH : ∀ {Σ} {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (A : Algebra {ℓ₁} {ℓ₂} Σ) →
             (B : Algebra {ℓ₃} {ℓ₄} Σ) → (h : Homo A B) →
             (A / Kernel h) ≅ homImg A h
iso-A/kerH {Σ} A B h = record { iso = f }
  where i : ∀ s → _ ⟶ _
        i s = record { _⟨$⟩_ = λ x → ′ h ′ s ⟨$⟩ x , x , refl (B ⟦ s ⟧ₛ)
                   ; cong = F.id
                   }
        j : ∀ s → _ ⟶ _
        j s = record { _⟨$⟩_ = proj₁ ∘ proj₂
                     ; cong = λ { {a , u , eq} {b , v , eq'} a≈b →
                       begin
                       ′ h ′ s ⟨$⟩ u
                       ≈⟨ eq ⟩
                       a
                       ≈⟨ a≈b ⟩
                       b
                       ≈⟨ Setoid.sym (B ⟦ s ⟧ₛ) eq' ⟩
                       ′ h ′ s ⟨$⟩ v
                       ∎
                     }
                     }
           where open EqR (B ⟦ s ⟧ₛ)
        i-cond : homCond (A / Kernel h) (homImg A h) i
        i-cond {ar} {s} f as = begin
                    ′ h ′ s ⟨$⟩ (A ⟦ f ⟧ₒ ⟨$⟩ as)
                    ≈⟨ cond h f as ⟩
                    B ⟦ f ⟧ₒ ⟨$⟩ map (λ s' a → ′ h ′ s' ⟨$⟩ a) as
                    ≈⟨ Π.cong (B ⟦ f ⟧ₒ) (eq-as as) ⟩
                    B ⟦ f ⟧ₒ ⟨$⟩ map (λ _ → proj₁) (map (λ s' → i s' ⟨$⟩_) as)
                    ∎
          where open EqR (B ⟦ s ⟧ₛ)
                eq-as : ∀ {ar : List (sorts Σ)} (as : HVec (λ s' → ∥ A ⟦ s' ⟧ₛ ∥) ar) →
                  _≈_ ((λ s' → B ⟦ s' ⟧ₛ) ✳ ar)
                    (map (λ s' a → ′ h ′ s' ⟨$⟩ a) as)
                    (map (λ _ → proj₁) (map (λ s' → i s' ⟨$⟩_) as))
                eq-as {[]} ⟨⟩ = ∼⟨⟩
                eq-as {s' ∷ _} (v ▹ as') = ∼▹ (Setoid.refl (B ⟦ s' ⟧ₛ)) (eq-as as')
        F : Homo (A / Kernel h) (homImg A h)
        F = record { ′_′ = i
                   ; cond = i-cond
                   }
        f : Isomorphism (A / Kernel h) (homImg A h)
        f = record { hom = F
                   ; bij = λ s → record { injective = F.id
                             ; surjective = record { from = j s
                                                   ; right-inverse-of = proj₂ ∘ proj₂
                                                   }
                             }
                   }
