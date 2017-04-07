module UnivAlgebra where

open import Relation.Binary hiding (Total)
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Nat renaming (_⊔_ to _⊔ₙ_)
open import Data.Product renaming (map to pmap)
open import Function as F
open import Function.Equality as FE renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Data.Bool renaming (_≟_ to _≟b_)
open import Data.List renaming (map to lmap)
open import Relation.Binary.PropositionalEquality as PE hiding ( Reveal_·_is_;[_];isEquivalence)

open import Data.Fin hiding (_+_)

import Relation.Binary.EqReasoning as EqR

open import HeterogeneousVec

pattern _↦_ ar s = (ar , s)

open Setoid
open import Setoids

record Signature : Set₁ where 
  field
    sorts  : Set
    ops    : (List sorts) × sorts → Set

  Arity : Set
  Arity = List sorts

  Type : Set
  Type = List sorts × sorts

open Signature



record Algebra {ℓ₁ ℓ₂ : Level} (Σ : Signature) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  constructor _∥_

  field
    _⟦_⟧ₛ   : sorts Σ → Setoid ℓ₁ ℓ₂
    _⟦_⟧ₒ    : ∀ {ar s} → ops Σ (ar , s) →
                _⟦_⟧ₛ ✳ ar ⟶ _⟦_⟧ₛ s

  _⟦_⟧ₛ* : (ar : Arity Σ) → Set _
  _⟦_⟧ₛ* ar = ∥ _⟦_⟧ₛ ✳ ar ∥

{-
private
  module example where
    data S : Set where nat : S ; bool : S

    data O : (List S) × S → Set where
      consℕ  : (n : ℕ) → O ([] , nat)
      True False  : O ([] , bool)
      plus    : O ( nat ∷ [ nat ] , nat)
      eq     : O ( nat ∷ [ nat ] , bool)
      cand   : O ( bool ∷ [ bool ] , bool)

    Sig₁ : Signature
    Sig₁ = record { sorts = S ; ops = O }

    open import Data.List.All
    data isMonoSorted : S → Arity Sig₁ → Set where
      monoSort : ∀ s ar → All (λ s' → s ≡ s') ar → isMonoSorted s ar
        
    data monoSorted {ar s} : ops Sig₁ (ar , s) → Set where
     isMono : ∀ (o : ops Sig₁ (ar , s)) → All (_≡_ s) ar → monoSorted o

    monoNat : ∀ {ar} → (o : O (ar , nat)) → monoSorted o
    monoNat (consℕ n) = isMono (consℕ n) []
    monoNat plus = isMono plus (_≡_.refl ∷ _≡_.refl ∷ [])

    open import Data.Empty
    fail : (∀ {ar} → (o : O (ar , bool)) → monoSorted o) → ⊥
    fail prop = feq (prop eq)
      where feq : monoSorted eq → ⊥
            feq (isMono .eq (() ∷ x))

    iS : sorts Sig₁ → Setoid _ _
    iS nat   = setoid ℕ
    iS bool  = setoid Bool
    
    iO : ∀ {ar s} → ops Sig₁ (ar ↦ s) → (iS ✳ ar) ⟶ iS s
    iO (consℕ n)  = record  { _⟨$⟩_ = λ { ⟨⟩ → n } ; cong = {! !} }
    iO plus  = record { _⟨$⟩_ = λ {⟨⟨ n₁ , n₂ ⟩⟩ → n₁ + n₂} ; cong = {! !} }
    iO eq    = record { _⟨$⟩_ = λ {⟨⟨ n₁ , n₂ ⟩⟩ → ? } ; cong = {! !} }
    iO and   = record { _⟨$⟩_ = λ {⟨⟨ b₁ , b₂ ⟩⟩ → b₁ ∧ b₂} ; cong = {! !} }
             
    Alg₁ : Algebra Sig₁
    Alg₁ = ? -- record { _⟦_⟧ₛ = iS , _⟦_⟧ₒ = iO }
    
  module exMonAction where
    data So : Set where
      M : So
      S : So

    data O : (List So) × So → Set where
      unit  : O ([] , M)
      mult  : O (M ∷ [ M ] , M)
      act   : O (M ∷ [ S ] , S)

    MonAct : Signature
    MonAct = record { sorts = So ; ops = O }
-}


module Hom {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
       {Σ : Signature}
       (A : Algebra {ℓ₁} {ℓ₂} Σ) 
       (B : Algebra {ℓ₃} {ℓ₄} Σ) where 

  open Algebra

  -- Function between algebras
  _⟿_ : Set _
  _⟿_ = (s : sorts Σ) → A ⟦ s ⟧ₛ ⟶ B ⟦ s ⟧ₛ

  -- Map
  map⟿ : {ar : Arity Σ} → (m : _⟿_) →
           (ts : A ⟦ ar ⟧ₛ*) → B ⟦ ar ⟧ₛ*
  map⟿ {ar = ar} m ts = map (_⟨$⟩_ ∘ m) ts


  --Homomorphism condition
  homCond : {ty : Type Σ} →
            (h : _⟿_) → (f : ops Σ ty) → Set _
  homCond {ty = (ar , s)} h f =
            (as : A ⟦ ar ⟧ₛ*) → (h s ⟨$⟩ (A ⟦ f ⟧ₒ ⟨$⟩ as))
                             ≈ₛ 
                             (B ⟦ f ⟧ₒ ⟨$⟩ (map⟿ h as))
      where _≈ₛ_ : _
            _≈ₛ_ = _≈_ (B ⟦ s ⟧ₛ)

  ℓ' : _
  ℓ' = lsuc (ℓ₄ ⊔ ℓ₃ ⊔ ℓ₁ ⊔ ℓ₂)

  -- Homomorphism

  record Homo : Set ℓ' where
    field
      ′_′    : _⟿_
      cond  : ∀ {ty} (f : ops Σ ty) → homCond ′_′ f

  open Homo
  open ExtEq
  open IsEquivalence renaming (refl to ref;sym to symm;trans to tran)
  
  _≈ₕ_  : (H G : Homo) → Set _
  H ≈ₕ G = (s : sorts Σ) → (′ H ′ s) ≈→ (′ G ′ s)
                                               
  ≈A→B : (s : sorts Σ) → IsEquivalence (_≈→_ {A = A ⟦ s ⟧ₛ} {B = B ⟦ s ⟧ₛ})
  ≈A→B s = Equiv≈→ {A = A ⟦ s ⟧ₛ} {B = B ⟦ s ⟧ₛ}
  equiv≈ₕ : IsEquivalence _≈ₕ_
  equiv≈ₕ = record { refl = λ {h} s a → ref (≈A→B s)  {′ h ′ s} a
                   ; sym = λ {h} {g} eq s a → symm (≈A→B s)
                                              {′ h ′ s} {′ g ′ s} (eq s) a
                   ; trans = λ {f} {g} {h} eq eq' s a →
                                   tran (≈A→B s) {′ f ′ s} {′ g ′ s}
                                        {′ h ′ s} (eq s) (eq' s) a
                   }


module HomComp {ℓ₁ ℓ₂ ℓ₃ ℓ₄ l₅ l₆}
       {Σ : Signature}
       {A₀ : Algebra {ℓ₁} {ℓ₂} Σ}
       {A₁ : Algebra {ℓ₃} {ℓ₄} Σ}
       {A₂ : Algebra {l₅} {l₆} Σ} where

  open Algebra
  
  open Hom
  open Homo
  
  _∘ₕ_ : (H : Homo A₁ A₂) → (H₀ : Homo A₀ A₁) →
         Homo A₀ A₂
  _∘ₕ_  H₁ H₀ = record { ′_′   = comp
                       ; cond  = ∘ₕcond
                       }
        where comp : A₀ ⟿ A₂
              comp s = ′ H₁ ′ s ∘ₛ ′ H₀ ′ s
  
              ∘ₕcond :  ∀ {ty} (f : ops Σ ty) → homCond A₀ A₂ comp f
              ∘ₕcond {ar , s} f as = 
                begin
                  comp s ⟨$⟩ (A₀ ⟦ f ⟧ₒ ⟨$⟩ as)
                    ≈⟨ Π.cong (′ H₁ ′ s) (p₀ as) ⟩
                  ′ H₁ ′ s ⟨$⟩ (A₁ ⟦ f ⟧ₒ ⟨$⟩ (map⟿ A₀ A₁ ′ H₀ ′ as))
                    ≈⟨ p₁ (map⟿ A₀ A₁ ′ H₀ ′ as) ⟩
                  A₂ ⟦ f ⟧ₒ ⟨$⟩ (map⟿  A₁ A₂ ′ H₁ ′ (map⟿ A₀ A₁ ′ H₀ ′ as))
                    ≈⟨ propMapMorph ⟩
                  A₂ ⟦ f ⟧ₒ ⟨$⟩ map⟿ A₀ A₂ comp as
                ∎
                where open EqR (A₂ ⟦ s ⟧ₛ)
                      ty = (ar , s)
                      p₁ = cond H₁ f
                      p₀ = cond H₀ f
                      propMapMorph = 
                        begin
                          A₂ ⟦ f ⟧ₒ ⟨$⟩ (map⟿ A₁ A₂ (′ H₁ ′) $
                                              map⟿  A₀ A₁ (′ H₀ ′) as)
                            ≈⟨ ≡to≈ (A₂ ⟦ s ⟧ₛ) $ PE.cong (A₂ ⟦ f ⟧ₒ ⟨$⟩_ )
                                              (propMapV∘ as (_⟨$⟩_ ∘ ′ H₀ ′)
                                              (_⟨$⟩_ ∘ ′ H₁ ′)) ⟩
                          A₂ ⟦ f ⟧ₒ ⟨$⟩ (map⟿ A₀ A₂ comp as)
                        ∎




-- Homomorphism identity
HomId : ∀ {ℓ₁ ℓ₂} {Σ} {A : Algebra {ℓ₁} {ℓ₂} Σ} →
          Hom.Homo A A
HomId {A = A} = record { ′_′ = λ s → FE.id
                       ; cond = λ { {ar , s} f as →
                                    Π.cong (A ⟦ f ⟧ₒ)
                                    (≡to∼v (λ i → Setoid.isEquivalence (A ⟦ i ⟧ₛ))
                                    (PE.sym (mapId as))) }
                       }
      where open Hom
            open Homo
            open Algebra


module HomLaws {ℓ₁ ℓ₂ ℓ₃ ℓ₄ l₅ l₆ l₇ l₈}
       {Σ : Signature}
       {A₀ : Algebra {ℓ₁} {ℓ₂} Σ}
       {A₁ : Algebra {ℓ₃} {ℓ₄} Σ}
       {A₂ : Algebra {l₅} {l₆} Σ}
       {A₃ : Algebra {l₇} {l₈} Σ} where

  open Algebra

  module _ where
    open HomComp
    open Hom A₀ A₁
    right-unit : (H : Homo ) → (H ∘ₕ HomId {A = A₀}) ≈ₕ H
    right-unit H s a = Setoid.refl (A₁ ⟦ s ⟧ₛ)

  module _ where
    open HomComp
    open Hom A₀ A₁
    left-unit : (H : Homo ) → (HomId {A = A₁} ∘ₕ H) ≈ₕ H
    left-unit H s a = Setoid.refl (A₁ ⟦ s ⟧ₛ)

  module _ where
    open HomComp
    open Hom hiding (_≈ₕ_)
    open Hom A₀ A₃ using (_≈ₕ_)
    assoc : (F : Homo A₀ A₁) (G : Homo A₁ A₂) (H : Homo A₂ A₃) →
            ((H ∘ₕ G) ∘ₕ F) ≈ₕ (H ∘ₕ (G ∘ₕ F))
    assoc F G H s a = Setoid.refl (A₃ ⟦ s ⟧ₛ)        

open import Function.Bijection renaming (_∘_ to _∘b_) 
open import Function.Surjection hiding (_∘_)

open Bijective

open Hom
open Homo
open Algebra
invHomo : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Σ : Signature} → 
          (A : Algebra {ℓ₁} {ℓ₂} Σ) → (A' : Algebra {ℓ₃} {ℓ₄} Σ) →
          (h : Homo A A') → (bj : (s : sorts Σ) → Bijective (′ h ′ s)) →
          Homo A' A
invHomo {Σ = Σ} A A' h bj = record { ′_′ = h⁻¹
                                   ; cond = cond⁻¹
                                   }
  where h⁻¹ : A' ⟿ A
        h⁻¹ s =  from (bj s)
        cond⁻¹ : ∀ {ty} (f : ops Σ ty) → homCond A' A h⁻¹ f
        cond⁻¹ {ar , s} f as = 
               begin
                 h⁻¹ s ⟨$⟩ ((A' ⟦ f ⟧ₒ) ⟨$⟩ as)
               ≈⟨ Π.cong (h⁻¹ s) (Π.cong (A' ⟦ f ⟧ₒ)
                         (∼↑v (λ i a' → Setoid.sym (A' ⟦ i ⟧ₛ) (right-inverse-of (bj i) a'))
                         as)) ⟩
                 h⁻¹ s ⟨$⟩ ((A' ⟦ f ⟧ₒ) ⟨$⟩ map (λ i a' → ′ h ′ i ⟨$⟩ (h⁻¹ i ⟨$⟩ a')) as)
               ≈⟨ Π.cong (h⁻¹ s) (Π.cong (A' ⟦ f ⟧ₒ)
                 (Setoid.sym (_⟦_⟧ₛ A' ✳ ar) (≡to≈ (_⟦_⟧ₛ A' ✳ ar) (propMapV∘ as (λ i → _⟨$⟩_ (h⁻¹ i))
                                                                               (λ i → _⟨$⟩_ (′ h ′ i)))))) ⟩
                 h⁻¹ s ⟨$⟩ ((A' ⟦ f ⟧ₒ) ⟨$⟩ map (λ i → _⟨$⟩_ (′ h ′ i)) (map (λ i → _⟨$⟩_ (h⁻¹ i)) as))
               ≈⟨ Π.cong (h⁻¹ s) (Setoid.sym (A' ⟦ s ⟧ₛ) (cond h f (map (λ i → _⟨$⟩_ (h⁻¹ i)) as))) ⟩
                 h⁻¹ s ⟨$⟩ (′ h ′ s ⟨$⟩ (A ⟦ f ⟧ₒ ⟨$⟩ (map (λ i → _⟨$⟩_ (h⁻¹ i)) as)))
               ≈⟨ left-inverse-of (bj s) (A ⟦ f ⟧ₒ ⟨$⟩ (map (λ i → _⟨$⟩_ (h⁻¹ i)) as)) ⟩
                 A ⟦ f ⟧ₒ ⟨$⟩ map⟿ A' A h⁻¹ as
               ∎
          where open EqR (A ⟦ s ⟧ₛ)



record Isomorphism {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Σ : Signature}
                   (A : Algebra {ℓ₁} {ℓ₂} Σ) (A' : Algebra {ℓ₃} {ℓ₄} Σ) : 
                                    Set (lsuc (ℓ₄ ⊔ ℓ₃ ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    hom : Homo A A'
    bij : (s : sorts Σ) → Bijective (′ hom ′ s)

open Isomorphism

-- Isomorphic algebras
record _≅_ {Σ} {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (A : Algebra {ℓ₁} {ℓ₂} Σ)
               (B : Algebra {ℓ₃} {ℓ₄} Σ) : Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
  field
    iso : Isomorphism A B

{- The relation of isomorphism between algebras is an equivalence relation -}

reflIso : ∀ {ℓ₁ ℓ₂ Σ} → Reflexive (Isomorphism {ℓ₁} {ℓ₂} {ℓ₁} {ℓ₂} {Σ})
reflIso {Σ = Σ} {A} = record { hom = HomId
                              ; bij = λ s → record { injective = F.id
                                                    ; surjective = surj s } }
  where surj : (s : sorts Σ) → Surjective (′ HomId {A = A} ′ s)
        surj s = record { from = FE.id
                        ; right-inverse-of = λ x → Setoid.refl (A ⟦ s ⟧ₛ) }

symIso : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Σ : Signature} → 
          (A : Algebra {ℓ₁} {ℓ₂} Σ) → (A' : Algebra {ℓ₃} {ℓ₄} Σ) →
          Isomorphism A A' → Isomorphism A' A
symIso {Σ = Σ} A A' i = record { hom = h⁻¹
                               ; bij = bij⁻¹ }
  where h⁻¹ : Homo A' A
        h⁻¹ = invHomo A A' (hom i) (bij i)
        surj⁻¹ : (s : sorts Σ) → Surjective (′ h⁻¹ ′ s)
        surj⁻¹ s = record { from = ′ hom i ′ s
                          ; right-inverse-of = left-inverse-of (bij i s)
                          }
        bij⁻¹ : (s : sorts Σ) → Bijective (′ h⁻¹ ′ s)
        bij⁻¹ s = record { injective = λ {x} {y} h⁻¹x≈h⁻¹y →
                             begin
                               x
                             ≈⟨ Setoid.sym (A' ⟦ s ⟧ₛ) (right-inverse-of (bij i s) x) ⟩
                               ′ hom i ′ s ⟨$⟩ (′ h⁻¹ ′ s ⟨$⟩ x)
                             ≈⟨ Π.cong (′ hom i ′ s) h⁻¹x≈h⁻¹y ⟩
                               ′ hom i ′ s ⟨$⟩ (′ h⁻¹ ′ s ⟨$⟩ y)
                             ≈⟨ right-inverse-of (bij i s) y ⟩
                               y
                             ∎
                         ; surjective = surj⁻¹ s }
              where open EqR (A' ⟦ s ⟧ₛ)

transIso : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆} {Σ : Signature} → 
             (A₀ : Algebra {ℓ₁} {ℓ₂} Σ) → (A₁ : Algebra {ℓ₃} {ℓ₄} Σ) →
             (A₂ : Algebra {ℓ₅} {ℓ₆} Σ) →
             Isomorphism A₀ A₁ → Isomorphism A₁ A₂ → Isomorphism A₀ A₂
transIso {Σ = Σ} A₀ A₁ A₂ iso₀ iso₁ =
            record { hom = hom iso₁ ∘ₕ hom iso₀
                   ; bij = λ s → bijective (bj₁ s ∘b bj₀ s) }
  where open HomComp
        open Bijection
        bj₀ : (s : sorts Σ) → Bijection (A₀ ⟦ s ⟧ₛ) (A₁ ⟦ s ⟧ₛ)
        bj₀ s = record { to = ′ hom iso₀ ′ s
                       ; bijective = bij iso₀ s }
        bj₁ : (s : sorts Σ) → Bijection (A₁ ⟦ s ⟧ₛ) (A₂ ⟦ s ⟧ₛ)
        bj₁ s = record { to = ′ hom iso₁ ′ s
                       ; bijective = bij iso₁ s }
        

-- Theorem 2.10 del Handbook. Debo poner los mismos niveles en ambas
-- algebras para que pueda ser una relación binaria en un mismo tipo.
isoEquiv : ∀ {ℓ₁ ℓ₂} {Σ} → IsEquivalence (Isomorphism {ℓ₁} {ℓ₂} {ℓ₁} {ℓ₂} {Σ})
isoEquiv {Σ = Σ} = record { refl = reflIso
                          ; sym = λ {A} {A'} i → symIso A A' i
                          ; trans = λ {A₀} {A₁} {A₂} i₀ i₁ →
                                           transIso A₀ A₁ A₂ i₀ i₁
                          }



{- Theo 2.11 -}
theo211 : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆} {Σ : Signature} → 
             (A : Algebra {ℓ₁} {ℓ₂} Σ) → (B : Algebra {ℓ₃} {ℓ₄} Σ) →
             (C : Algebra {ℓ₅} {ℓ₆} Σ) → A ≅ B →
             (Homo B C → Homo A C) × (Homo C B → Homo C A)
theo211 A B C A≅B = (λ h → h ∘ₕ hom i) ,
                    (λ h → invHomo A B (hom i) (bij i) ∘ₕ h)
  where open HomComp
        open _≅_
        i : Isomorphism A B
        i = iso A≅B


Total : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → Rel A ℓ₂ → Set _ 
Total _≈_ = ∀ a a' → a ≈ a'

private
  module _ where

  totalIsEquiv : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → (R : Rel A ℓ₂) → Total R → IsEquivalence R
  totalIsEquiv R tot = record { refl = λ {x} → tot x x
                              ; sym = λ {x} {y} _ → tot y x
                              ; trans = λ {x} {y} {z} _ _ → tot x z
                              }

Unique : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → Rel A ℓ₂ → Set _
Unique {A = A} _≈_ = A × Total _≈_

Unique' : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → (_≈_ : Rel A ℓ₂) →
            IsEquivalence _≈_ → Set _
Unique' {A = A} _≈_ _ = ∀ a a' → a ≈ a'

module Initial (Σ : Signature)
               {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} where

  open Hom
  open Algebra

  record Initial  : Set (lsuc (ℓ₄ ⊔ ℓ₃ ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      alg   : Algebra {ℓ₁} {ℓ₂} Σ
      init  : (A : Algebra {ℓ₃} {ℓ₄} Σ) → Unique (_≈ₕ_ alg A)

  private
    Initial' : ∀ {ℓ₁ ℓ₂} (A : Algebra {ℓ₁} {ℓ₂} Σ) →  {ℓ₃ ℓ₄ : Level} → Set _
    Initial' A {ℓ₃} {ℓ₄} = ∀ (B : Algebra {ℓ₃} {ℓ₄} Σ) → Unique (_≈ₕ_ A B)


module Final (Σ : Signature)
             {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} where
  open Hom
  open Algebra

  record Final  : Set (lsuc (ℓ₄ ⊔ ℓ₃ ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      alg   : Algebra {ℓ₁} {ℓ₂} Σ
      init  : (A : Algebra {ℓ₃} {ℓ₄} Σ) → Unique (_≈ₕ_ A alg)


module TermAlgebra (Σ : Signature) where

  open Hom
  open Algebra

  data HU : (s : sorts Σ) → Set where
    term : ∀  {ar s} →  (f : ops Σ (ar ↦ s)) → (HVec HU ar) → HU s

  ∣T∣ : Algebra Σ
  ∣T∣ = record  { _⟦_⟧ₛ = setoid ∘ HU
               ; _⟦_⟧ₒ  = ∣_|ₒ
               }
    where ≡vec : ∀ {ar}  → (ts₁ ts₂ : HVec HU ar) →
                 _∼v_ {R = λ _ → _≡_} ts₁ ts₂ →
                 ts₁ ≡ ts₂
          ≡vec ⟨⟩ ⟨⟩ ≈⟨⟩ = PE.refl
          ≡vec (t ▹ ts₁) (.t ▹ ts₂) (∼▹ PE.refl ts₁≈ts₂) =
                                        PE.cong (λ ts → t ▹ ts)
                                                (≡vec ts₁ ts₂ ts₁≈ts₂)
          fcong : ∀ {ar s} {f : ops Σ (ar ↦ s)} →
                           (ts₁ ts₂ : HVec HU ar) →
                           _∼v_ {R = λ s₀ → _≡_} ts₁ ts₂ →
                           term f ts₁ ≡ term f ts₂
          fcong {f = f} ts₁ ts₂ ts₁≈ts₂ = PE.cong (term f) (≡vec ts₁ ts₂ ts₁≈ts₂)
          ∣_|ₒ  : ∀ {ar s} → ops Σ (ar ↦ s) → (setoid ∘ HU) ✳ ar ⟶ (setoid ∘ HU) s
          ∣ f |ₒ = record { _⟨$⟩_ = term f
                         ; cong = λ {ts₁} {ts₂} ts₁≈ts₂ → fcong ts₁ ts₂ ts₁≈ts₂
                         }

module InitTermAlg (Σ : Signature) where 

  open Algebra
  open TermAlgebra Σ
  open Hom
  open Homo

  mutual
    ∣h∣→A : ∀ {ℓ₁ ℓ₂ s} → (A : Algebra {ℓ₁} {ℓ₂} Σ) → HU s → ∥ A ⟦ s ⟧ₛ ∥
    ∣h∣→A A (term f ⟨⟩)         =   A ⟦ f ⟧ₒ ⟨$⟩ ⟨⟩
    ∣h∣→A A (term f (t ▹ ts))  =   A ⟦ f ⟧ₒ ⟨$⟩ (∣h∣→A A t ▹ map|h|→A A ts)
  
    map|h|→A : ∀ {ℓ₁ ℓ₂ ar} → (A : Algebra {ℓ₁} {ℓ₂} Σ)
                             → ∣T∣ ⟦ ar ⟧ₛ* → A ⟦ ar ⟧ₛ*
    map|h|→A A ⟨⟩ = ⟨⟩
    map|h|→A A (t ▹ ts) = ∣h∣→A A t ▹ map|h|→A A ts


  map|T|→A≡map : ∀ {ℓ₁ ℓ₂ ar} {ts : ∣T∣ ⟦ ar ⟧ₛ*} {A : Algebra {ℓ₁} {ℓ₂} Σ} →
                   map|h|→A A ts ≡ map (λ s → ∣h∣→A A) ts
  map|T|→A≡map {ar = []} {⟨⟩} {A} = PE.refl
  map|T|→A≡map {ar = s ∷ ar} {t ▹ ts} {A} =
                  PE.cong (λ ts' → ∣h∣→A A t ▹ ts') map|T|→A≡map

  ∣H∣ : ∀ {ℓ₁ ℓ₂} → (A : Algebra {ℓ₁} {ℓ₂} Σ) → Homo ∣T∣ A
  ∣H∣ A = record { ′_′  = fun|T|ₕ
               ; cond = |T|ₕcond
               }
    where congfun : ∀ {s} {t₁ t₂ : HU s} →
                    t₁ ≡ t₂ → _≈_ (A ⟦ s ⟧ₛ) (∣h∣→A A t₁) (∣h∣→A A t₂)
          congfun {s} t₁≡t₂ = ≡to≈ (A ⟦ s ⟧ₛ) (PE.cong (∣h∣→A A) t₁≡t₂)
          fun|T|ₕ : ∣T∣ ⟿ A
          fun|T|ₕ s = record { _⟨$⟩_ = ∣h∣→A {s = s} A
                             ; cong  = congfun {s}
                             }
          |T|ₕcond : ∀ {ty} (f : ops Σ ty) → (homCond ∣T∣ A) fun|T|ₕ f
          |T|ₕcond {_ ↦ s} f ⟨⟩ = ≡to≈ (A ⟦ s ⟧ₛ) PE.refl
          |T|ₕcond {_ ↦ s} f (t ▹ ts) =
                   ≡to≈ (A ⟦ s ⟧ₛ) (PE.cong (λ ts' → A ⟦ f ⟧ₒ ⟨$⟩
                                   (∣h∣→A A t ▹ ts')) map|T|→A≡map)


  total : ∀ {ℓ₁ ℓ₂} → (A : Algebra {ℓ₁} {ℓ₂} Σ) → Total (_≈ₕ_ ∣T∣ A)
  total A H G s (term {ar = ar} f ts) = 
            begin
              ′ H ′ s ⟨$⟩ term f ts
                ≈⟨ cond H f ts ⟩
              A ⟦ f ⟧ₒ ⟨$⟩ (map⟿ ∣T∣ A ′ H ′ ts)
                ≈⟨ Π.cong (A ⟦ f ⟧ₒ) (map≈ ar ts) ⟩
              A ⟦ f ⟧ₒ ⟨$⟩ (map⟿ ∣T∣ A ′ G ′ ts)
                ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (cond G f ts) ⟩ 
              ′ G ′ s ⟨$⟩ term f ts
            ∎
    where open EqR (A ⟦ s ⟧ₛ)
          map≈ : (ar : Arity Σ) → (ts : HVec (HU) ar) →
                 (map (_⟨$⟩_ ∘ ′ H ′) ts) ∼v (map (_⟨$⟩_ ∘ ′ G ′) ts)
          map≈ [] ⟨⟩ = ∼⟨⟩
          map≈ (s ∷ ar) (t ▹ ts) = ∼▹ (total A H G s t)
                                      (map≈ ar ts)


  open Initial Σ

  ∣T∣isInitial : ∀ {ℓ₁ ℓ₂} → Initial {ℓ₃ = ℓ₁} {ℓ₄ = ℓ₂}
  ∣T∣isInitial = record  { alg = ∣T∣
                        ; init = λ A → ∣H∣ A , total A }

open import Relation.Binary.Product.Pointwise using (_×-setoid_)

module ProdAlg {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
        {Σ : Signature}
       (A : Algebra {ℓ₁} {ℓ₂} Σ) 
       (B : Algebra {ℓ₃} {ℓ₄} Σ) where

  std : (s : sorts Σ) → Setoid _ _
  std s = (A ⟦ s ⟧ₛ) ×-setoid (B ⟦ s ⟧ₛ)
  _≈*_ : {ar : Arity Σ} → _
  _≈*_ {ar} = _≈_ (std ✳ ar)
  -- these two proofs should be abstracted.
  ≈₁ : ∀ {ar} {vs vs' : ∥ std ✳ ar ∥} 
      → vs ≈* vs' → _≈_ (_⟦_⟧ₛ A ✳ ar) (map (λ _ → proj₁) vs) (map (λ _ → proj₁) vs')
  ≈₁ {[]} ∼⟨⟩ = ∼⟨⟩
  ≈₁ {i ∷ is} (∼▹ (eq , _) equ) = ∼▹ eq (≈₁ equ)
  ≈₂ : ∀ {ar} {vs vs' : ∥ std ✳ ar ∥} 
      → vs ≈* vs' → _≈_ (_⟦_⟧ₛ B ✳ ar) (map (λ _ → proj₂) vs) (map (λ _ → proj₂) vs')
  ≈₂ {[]} ∼⟨⟩ = ∼⟨⟩
  ≈₂ {i ∷ is} (∼▹ (_ , eq) equ) = ∼▹ eq (≈₂ equ)

  {- Product of algebras -}
  _×-alg_ : Algebra {ℓ₃ ⊔ ℓ₁} {ℓ₄ ⊔ ℓ₂} Σ
  _×-alg_ = record {
            _⟦_⟧ₛ = λ s → (A ⟦ s ⟧ₛ) ×-setoid (B ⟦ s ⟧ₛ)
          ; _⟦_⟧ₒ = λ {ar} {s} f → record { _⟨$⟩_ = if f ; cong = cng f}
          }
    where if : ∀ {ar s} (f : ops Σ (ar , s)) → _ → _
          if {ar} {s} f vs =  A ⟦ f ⟧ₒ ⟨$⟩ map (λ _ → proj₁) vs
                            , B ⟦ f ⟧ₒ ⟨$⟩ map (λ _ → proj₂) vs
          cng : ∀ {ar s} (f : ops Σ (ar , s)) → {vs vs' : ∥ std ✳ ar ∥} 
              → vs ≈* vs' → _≈_ (std s) (if f vs) (if f vs')
          cng {ar} f equ = (Π.cong (_⟦_⟧ₒ A f) (≈₁ equ)) ,
                           ((Π.cong (_⟦_⟧ₒ B f) (≈₂ equ)))

  {- Projections -}
  Π₁ : Homo _×-alg_ A
  Π₁ = record { ′_′ = λ s → record { _⟨$⟩_ = proj₁ ; cong = λ { (eq , _) → eq }}
              ; cond = λ { {ar , s} f as → Setoid.refl (A ⟦ s ⟧ₛ ) }
              }

  {- Projections -}
  Π₂ : Homo _×-alg_ B
  Π₂ = record { ′_′ = λ s → record { _⟨$⟩_ = proj₂ ; cong = λ { (_ , eq) → eq }}
              ; cond = λ { {ar , s} f as → Setoid.refl (B ⟦ s ⟧ₛ ) }
              }


open import Relation.Unary hiding (_⊆_;_⇒_)

OpClosed : ∀ {ℓ₁ ℓ₂ ℓ₃ Σ} → (A : Algebra {ℓ₁} {ℓ₂} Σ) →
                  (P : (s : sorts Σ) → Pred (∥ A ⟦ s ⟧ₛ ∥) ℓ₃) → Set _
OpClosed {ℓ₃ = ℓ₃} {Σ = Σ} A P = ∀ {ar s} (f : ops Σ (ar , s)) →
             (P ⇨v ⟨→⟩ P s) (A ⟦ f ⟧ₒ ⟨$⟩_)

private
  module _ {ℓ₃ ℓ₁ ℓ₂} {Σ : Signature} (A : Algebra {ℓ₁} {ℓ₂} Σ)
           (rel : (s : sorts Σ) → Rel (Carrier (A ⟦ s ⟧ₛ)) ℓ₃)
           (req : (s : sorts Σ) → IsEquivalence (rel s))
           (wd : (s : sorts Σ) → WellDefRel (A ⟦ s ⟧ₛ) (rel s)) where

    open ProdAlg
    substi : Set _
    substi =  ∀ {ar s} (f : ops Σ (ar , s)) → rel * =[ A ⟦ f ⟧ₒ ⟨$⟩_ ]⇒ rel s

    pred' : (s : sorts Σ) → Pred (∥ (A ×-alg A) ⟦ s ⟧ₛ ∥) ℓ₃
    pred' s = λ {(a , a') → rel s a a'}
    
    -- Claim: substi ↔ OpClosed (A ×-alg A) pred'

record Congruence {ℓ₃ ℓ₁ ℓ₂} {Σ : Signature}
                  (A : Algebra {ℓ₁} {ℓ₂} Σ) : Set (lsuc ℓ₃ ⊔ ℓ₂ ⊔ ℓ₁) where
  field
    rel : (s : sorts Σ) → Rel (Carrier (A ⟦ s ⟧ₛ)) ℓ₃
    welldef : (s : sorts Σ) → WellDefRel (A ⟦ s ⟧ₛ) (rel s)
    cequiv : (s : sorts Σ) → IsEquivalence (rel s)
    csubst : ∀ {ar s} (f : ops Σ (ar , s)) → rel * =[ A ⟦ f ⟧ₒ ⟨$⟩_ ]⇒ rel s


open Congruence


_⊆_ : ∀ {ℓ₃ ℓ₁ ℓ₂} {Σ : Signature} {A : Algebra {ℓ₁} {ℓ₂} Σ} →
        Congruence {ℓ₃} A → Congruence {ℓ₃} A → Set _
Φ ⊆ Ψ = ∀ s → (rel Φ s) ⇒ (rel Ψ s)

-- Quotient Algebra
_/_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {Σ} → (A : Algebra {ℓ₁} {ℓ₂} Σ) → (C : Congruence {ℓ₃} A) →
                            Algebra {ℓ₁} {ℓ₃} Σ
A / C = (λ s → record { Carrier = Carrier (A ⟦ s ⟧ₛ)
                              ; _≈_ = rel C s
                              ; isEquivalence = cequiv C s })
               ∥
               (λ {ar} {s} f → record { _⟨$⟩_ = λ v → A ⟦ f ⟧ₒ ⟨$⟩ v
                                      ; cong = csubst C f } )

-- Subalgebras

open SetoidPredicate

record SubAlg {ℓ₃ ℓ₁ ℓ₂} {Σ} (A : Algebra {ℓ₁} {ℓ₂} Σ) :
                                          Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where

  field
    pr   : (s : sorts Σ) → SetoidPredicate {ℓ₃ = ℓ₃} (A ⟦ s ⟧ₛ)
    opClosed : OpClosed {Σ = Σ} A (λ s x → predicate (pr s) x)
    
  pcong : ∀ {ar} {v₁ v₂ : HVec (λ s → Carrier $ SubSetoid (A ⟦ s ⟧ₛ) (predicate (pr s))) ar} →
                           _∼v_ {l₁ = ℓ₂} {R = λ s x x₁ → Setoid._≈_ (A ⟦ s ⟧ₛ) (proj₁ x) (proj₁ x₁)} {is = ar} v₁ v₂ →
                           _∼v_ {l₁ = ℓ₂} {R = λ s → Setoid._≈_ (A ⟦ s ⟧ₛ)} (map (λ _ → proj₁) v₁ ) (map (λ _ → proj₁) v₂)
  pcong {[]} {⟨⟩} ∼⟨⟩ = ∼⟨⟩
  pcong {i ∷ is} (∼▹ x eq) = ∼▹ x (pcong eq)
  

SubAlgebra : ∀ {Σ} {ℓ₁ ℓ₂ ℓ₃} {A : Algebra {ℓ₁} {ℓ₂} Σ} →
                   SubAlg {ℓ₃ = ℓ₃} A → Algebra Σ
SubAlgebra {Σ} {A = A} S = is ∥ if 
           where
             open SubAlg S 
             is : sorts Σ → _
             is s = SubSetoid (A ⟦ s ⟧ₛ) (predicate (pr s))
             if : ∀ {ar} {s} → (f : ops Σ (ar , s)) → is ✳ ar ⟶ is s
             if {ar} {s} f = record { _⟨$⟩_ = λ v → (A ⟦ f ⟧ₒ ⟨$⟩ map (λ _ → proj₁) v)
                                         , opClosed f (⇨₂ v)
                                  ; cong = λ { {v₁} {v₂} eq → Π.cong (A ⟦ f ⟧ₒ) (pcong eq) }
                                  }



{- Homomorphic image is a SubAlgebra of B -}

SubImg : ∀ {Σ} {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (A : Algebra {ℓ₁} {ℓ₂} Σ) →
                              (B : Algebra {ℓ₃} {ℓ₄} Σ) →
                              (h : Homo A B) → SubAlg B
SubImg {Σ} A B h = record { pr = subipr ; opClosed = subicond }
  where subiwdef : ∀ {s} {b₀ b₁} → _≈_ (B ⟦ s ⟧ₛ) b₀ b₁ →
                     ∃ (λ a → _≈_ (B ⟦ s ⟧ₛ) (′ h ′ s ⟨$⟩ a ) b₀) →
                     ∃ (λ a → _≈_ (B ⟦ s ⟧ₛ) (′ h ′ s ⟨$⟩ a ) b₁)
        subiwdef {s} {b₀} {b₁} eq (a , eq') = a ,
                     (begin
                            ′ h ′ s ⟨$⟩ a
                              ≈⟨ eq' ⟩
                            b₀
                              ≈⟨ eq ⟩
                            b₁
                          ∎
                     )
          where open EqR (B ⟦ s ⟧ₛ)
        subipr : (s : sorts Σ) → SetoidPredicate (B ⟦ s ⟧ₛ)
        subipr s = record { predicate = λ b → ∃ (λ a → _≈_ (B ⟦ s ⟧ₛ) (′ h ′ s ⟨$⟩ a ) b)
                          ; predWellDef = subiwdef }
        subicond : ∀ {ar} {s} → (f : ops Σ (ar , s)) →
                     (_⇨v_ (predicate ∘ subipr) ⟨→⟩ predicate (subipr s))
                     (_⟨$⟩_ (B ⟦ f ⟧ₒ))
        subicond {ar} {s} f v = (A ⟦ f ⟧ₒ ⟨$⟩ va) ,
                                (begin
                                  ′ h ′ s ⟨$⟩ (A ⟦ f ⟧ₒ ⟨$⟩ va)
                                ≈⟨ cond h f va ⟩
                                  B ⟦ f ⟧ₒ ⟨$⟩ (map⟿ A B ′ h ′ va)
                                ≈⟨ Π.cong (B ⟦ f ⟧ₒ) (p≈ v) ⟩
                                  B ⟦ f ⟧ₒ ⟨$⟩ proj₁⇨v v
                                ∎
                               )
          where open EqR (B ⟦ s ⟧ₛ)
                ⇨vΣ : HVec (λ sᵢ → Σ[ b ∈ Carrier (B ⟦ sᵢ ⟧ₛ) ] (predicate ∘ subipr) sᵢ b) ar
                ⇨vΣ  = ⇨vtoΣ v
                va : HVec (Carrier ∘ _⟦_⟧ₛ A) ar
                va = map (λ { i (b , a , ha≈b) → a }) ⇨vΣ
                p≈ : ∀ {ar'} {vs : HVec (Carrier ∘ _⟦_⟧ₛ B) ar'} → (pvs : (predicate ∘ subipr) ⇨v vs) → 
                     ((_⟦_⟧ₛ B ✳ ar') ≈
                     map⟿ A B ′ h ′ (map (λ { i (b , a , ha≈b) → a }) (⇨vtoΣ pvs)))
                     vs
                p≈ ⇨v⟨⟩ = ∼⟨⟩
                p≈ (⇨v▹ pv pvs) = ∼▹ (proj₂ pv) (p≈ pvs)

-- Definition 2.8
homImg : ∀ {Σ} {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {B : Algebra {ℓ₃} {ℓ₄} Σ} →
               (A : Algebra {ℓ₁} {ℓ₂} Σ) → (h : Homo A B) → Algebra Σ
homImg {Σ} {B = B} A h = SubAlgebra (SubImg A B h)


Kernel : ∀ {Σ} {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Algebra {ℓ₁} {ℓ₂} Σ} {B : Algebra {ℓ₃} {ℓ₄} Σ}
                             (h : Homo A B) →
                             Congruence {ℓ₃ = ℓ₄} A
Kernel {Σ} {ℓ₄ = ℓ₄} {A = A} {B} h =
       record { rel = krel
              ; welldef = λ {s {(x , y)} {(w , z)} eq p → krelWdef s (proj₁ eq) (proj₂ eq) p }
              ; cequiv = krelEquiv
              ; csubst = krsubst
              }
  where krel : (s : sorts Σ) → Rel (Carrier (A ⟦ s ⟧ₛ)) ℓ₄
        krel s = λ a₁ a₂ → _≈_ (B ⟦ s ⟧ₛ) (′ h ′ s ⟨$⟩ a₁ ) (′ h ′ s ⟨$⟩ a₂)
        krelWdef : ∀ s {x₁ x₂ y₁ y₂ : Carrier (A ⟦ s ⟧ₛ)} →
                   _≈_ (A ⟦ s ⟧ₛ) x₁ x₂ → _≈_ (A ⟦ s ⟧ₛ) y₁ y₂ →
                   krel s x₁ y₁ → krel s x₂ y₂
        krelWdef s {x₁} {x₂} {y₁} {y₂} eqx eqy x₁ry₁ =
                        begin
                          ′ h ′ s ⟨$⟩ x₂
                          ≈⟨ Setoid.sym (B ⟦ s ⟧ₛ) (Π.cong (′ h ′ s) eqx) ⟩
                          ′ h ′ s ⟨$⟩ x₁
                          ≈⟨ x₁ry₁ ⟩
                          ′ h ′ s ⟨$⟩ y₁
                          ≈⟨ Π.cong (′ h ′ s) eqy ⟩
                          ′ h ′ s ⟨$⟩ y₂
                         ∎
          where open EqR (B ⟦ s ⟧ₛ)
        krelEquiv : (s : sorts  Σ) → IsEquivalence (krel s)
        krelEquiv s = record { refl = Setoid.refl (B ⟦ s ⟧ₛ)
                             ; sym = Setoid.sym (B ⟦ s ⟧ₛ)
                             ; trans = Setoid.trans (B ⟦ s ⟧ₛ) }
        krsubst : {ar : List (sorts Σ)} {s : sorts Σ} (f : ops Σ (ar , s)) →
                  _∼v_ {R = krel} =[ _⟨$⟩_ (A ⟦ f ⟧ₒ) ]⇒ krel s
        krsubst {s = s} f {vs₁} {vs₂} eq =
                begin
                   ′ h ′ s ⟨$⟩ ((A ⟦ f ⟧ₒ) ⟨$⟩ vs₁)
                   ≈⟨ cond h f vs₁ ⟩
                   (B ⟦ f ⟧ₒ ⟨$⟩ (map⟿ A B ′ h ′ vs₁))
                   ≈⟨ Π.cong (B ⟦ f ⟧ₒ) (p eq) ⟩
                   (B ⟦ f ⟧ₒ ⟨$⟩ (map⟿ A B ′ h ′ vs₂))
                   ≈⟨ Setoid.sym (B ⟦ s ⟧ₛ) (cond h f vs₂) ⟩
                   ′ h ′ s ⟨$⟩ ((A ⟦ f ⟧ₒ) ⟨$⟩ vs₂)
                 ∎
          where open EqR (B ⟦ s ⟧ₛ)
                p : ∀ {is} {v w} → _∼v_ {R = krel} {is = is} v w →
                      _∼v_ {R = λ s' → _≈_ (B ⟦ s' ⟧ₛ)} {is = is}
                           (map⟿ A B ′ h ′ v)
                           (map⟿ A B ′ h ′ w)
                p {[]} ∼⟨⟩ = ∼⟨⟩
                p {i ∷ is} (∼▹ x eq₁) = ∼▹ x (p eq₁)

open import Relation.Binary.Product.Pointwise using (_×-setoid_)

QuotHom : ∀ {Σ} {ℓ₁ ℓ₂ ℓ₃} (A : Algebra {ℓ₁} {ℓ₂} Σ) →
                        (Q : Congruence {ℓ₃} A) → Homo A (A / Q)
QuotHom {Σ} A Q = record { ′_′ = fₕ
                         ; cond = condₕ }
  where fₕ : A ⟿ (A / Q)
        fₕ s = record { _⟨$⟩_ = F.id
                      ; cong = PC-resp-~ {S = A ⟦ s ⟧ₛ} (rel Q s) (welldef Q s , (cequiv Q s)) }
          where open IsEquivalence
        condₕ : ∀ {ty} (f : ops Σ ty) → homCond A (A / Q) fₕ f
        condₕ {ar , s} f as = subst ((rel Q s) (A ⟦ f ⟧ₒ ⟨$⟩ as))
                                    (PE.cong (_⟨$⟩_ (A ⟦ f ⟧ₒ)) mapid≡)
                                    (IsEquivalence.refl (cequiv Q s))
          where open IsEquivalence
                mapid≡ : ∀ {ar'} {as' : Carrier (_⟦_⟧ₛ A ✳ ar')} →
                         as' ≡ map (λ _ a → a) as'
                mapid≡ {as' = ⟨⟩} = PE.refl
                mapid≡ {as' = v ▹ as'} = PE.cong (λ as'' → v ▹ as'') mapid≡ 



    
open Surjective

-- Isomorphism Theorems
module FirstHomTheo {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Σ : Signature}
                     (A : Algebra {ℓ₁} {ℓ₂} Σ)
                     (B : Algebra {ℓ₃} {ℓ₄} Σ)
                     (h : Homo A B) where

 firstHomTheo : (surj : (s : sorts Σ) → Surjective (′ h ′ s)) → Isomorphism (A / Kernel h) B
 firstHomTheo surj =
             record { hom = homo₁
                    ; bij = bij₁
                    }
  where homo₁ : Homo (A / Kernel h) B
        homo₁ = record { ′_′ = λ s → record { _⟨$⟩_ = λ a → ′ h ′ s ⟨$⟩ a
                                            ; cong = F.id }
                       ; cond = λ { {ar , s} f as → cond h f as }
                       }
        surj₁ : (s : sorts Σ) → Surjective (′ homo₁ ′ s)
        surj₁ s = record { from = record { _⟨$⟩_ = λ b → Surjective.from
                                                                 (surj s) ⟨$⟩ b
                                         ; cong = λ {b} {b'} b≈b' → Π.cong (′ h ′ s)
                                                                    (Π.cong (Surjective.from (surj s)) b≈b') }
                         ; right-inverse-of = λ b → Surjective.right-inverse-of (surj s) b
                         }
        bij₁ : (s : sorts Σ) → Bijective (′ homo₁ ′ s)
        bij₁ s = record { injective = F.id
                        ; surjective = surj₁ s }



module SecondHomTheo {ℓ₁ ℓ₂ ℓ₃} {Σ : Signature}
                    (A : Algebra {ℓ₁} {ℓ₂} Σ)
                    (Φ Ψ : Congruence {ℓ₃} A)
                    (Ψ⊆Φ : Ψ ⊆ Φ )
                    where

  open IsEquivalence renaming (trans to tr ; sym to sy ; refl to re) 
  -- Φ/Ψ is a congruence on A/Ψ
  theo₁ : Congruence (A / Ψ)
  theo₁ = record { rel = λ {s x x₁ → rel Φ s x x₁ } 
                 ; welldef = λ { s {a , b} {c , d} (a~c , b~d) a~b →
                        tr (cequiv Φ s) (sy (cequiv Φ s) (Ψ⊆Φ s a~c))
                       (tr (cequiv Φ s) a~b ((Ψ⊆Φ s b~d))) }
                 ; cequiv = λ s → cequiv Φ s
                 ; csubst = csubst Φ
                 }

                 


  -- A/Φ is isomorphic to (A/Ψ)/(Φ/Ψ)
  theo₂ : Isomorphism (A / Φ) ((A / Ψ) / theo₁)
  theo₂ = record { hom = ho
                 ; bij = λ s → record { injective = λ x₁ → x₁
                                      ; surjective = record { from = act s
                                        ; right-inverse-of = λ x → re (cequiv Φ s) {x} }
                                      }
                 }
        where
              act : (A / Φ) ⟿ ((A / Ψ) / theo₁)
              act s = record { _⟨$⟩_ = F.id ; cong = λ x → x }
              condₕ : ∀ {ty} (f : ops Σ ty) →  homCond (A / Φ) ((A / Ψ) / theo₁) act f
              condₕ {ar , s} f as = subst ((rel Φ s) (A ⟦ f ⟧ₒ ⟨$⟩ as))
                                    (PE.cong (_⟨$⟩_ (A ⟦ f ⟧ₒ)) mapid≡)
                                    (IsEquivalence.refl (cequiv Φ s))
                where open IsEquivalence
                      mapid≡ : ∀ {ar'} {as' : Carrier (_⟦_⟧ₛ A ✳ ar')} →
                               as' ≡ map (λ _ a → a) as'
                      mapid≡ {as' = ⟨⟩} = PE.refl
                      mapid≡ {as' = v ▹ as'} = PE.cong (λ as'' → v ▹ as'') mapid≡ 

              ho : Homo (A / Φ) ((A / Ψ) / theo₁)
              ho = record { ′_′ = act
                          ; cond = condₕ
                          }


module ThirdHomTheo {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Σ : Signature}
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
                 ; csubst = λ f x → csubst Φ f (relπ₁ x)
                 }
        where wellDef : (s : sorts Σ) → WellDefRel (SubAlgebra B ⟦ s ⟧ₛ) (trace s)
              wellDef s (eq₁ , eq₂) a₁~a₂ = welldef Φ s (eq₁ , eq₂) a₁~a₂
              cEquiv :  (s : sorts Σ) → IsEquivalence (trace s)
              cEquiv s = record { refl = λ {x} → IsEquivalence.refl (cequiv Φ s) {proj₁ x}
                                ; sym = λ x → IsEquivalence.sym (cequiv Φ s) x
                                ; trans = λ x x₁ → IsEquivalence.trans (cequiv Φ s) x x₁ }
              relπ₁ : {ar : List (sorts Σ)} {i j : HVec (λ z → Carrier (SubAlgebra B ⟦ z ⟧ₛ)) ar} →
                         (eq : _∼v_ {R = trace } i j) → map (λ _ → proj₁) i ∼v map (λ _ → proj₁) j
              relπ₁ ∼⟨⟩ = ∼⟨⟩
              relπ₁ (∼▹ x eq) = ∼▹ x (relπ₁ eq)
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
  bs (i ∷ is) (v ▹ vs₁) (⇨v▹ ((b , pv) , bv) as₁) = (  (b , pv)) ▹ bs is vs₁ as₁
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
            mutual 

              cond⇉ : {ty : _} (f : ops Σ ty) →
                    homCond (SubAlgebra theo₂) (SubAlgebra B / theo₁) ⇉ f
              cond⇉  f as = csubst Φ f  (cond⇉* as)
              cond⇉* : ∀ {ar} as →  map (λ _ → proj₁) (bs ar (map (λ _ → proj₁) as)
                                                         (⇨₂ as))
                                    ∼v
                                 map (λ _ → proj₁) (map (( _⟨$⟩_) ∘ ⇉) as)
              cond⇉* {[]} ⟨⟩ = ∼⟨⟩
              cond⇉* {i ∷ is} (v ▹ as) = ∼▹ (ref (cequiv Φ i)) (cond⇉* as)


