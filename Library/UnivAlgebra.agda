module UnivAlgebra where

open import Relation.Binary hiding (Total ; _⇒_)
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Nat renaming (_⊔_ to _⊔ₙ_)
open import Data.Product renaming (map to pmap)
open import Function
open import Function.Equality renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Data.Bool
open import Data.List renaming (map to lmap)
open import Relation.Binary.PropositionalEquality as PE
open import Data.String hiding (setoid)
open import Data.Fin

import Relation.Binary.EqReasoning as EqR

open import HeterogenuousVec

pattern _⇒_ ar s = (ar , s)

open Setoid

∥_∥ : ∀ {l₁ l₂} → (Setoid l₁ l₂) → Set l₁
∥_∥ {l₁} {l₂} S = Carrier S


-- Extensional equality

module ExtEq {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Setoid ℓ₁ ℓ₂} {B : Setoid ℓ₃ ℓ₄} where
  private
    _≈B_ : _
    _≈B_ = _≈_ B

    _≈A_ : _
    _≈A_ = _≈_ A

  _≈→_ : Rel (A ⟶ B) _
  f ≈→ g  = ∀ (a : ∥ A ∥) → (f ⟨$⟩ a) ≈B (g ⟨$⟩ a)

  ≈→-preserves-≈ : ∀ a a' f g → f ≈→ g → a ≈A a' → (f ⟨$⟩ a) ≈B (g ⟨$⟩ a')
  ≈→-preserves-≈ a a' f g f≈g a≈a' =
                      begin
                        f ⟨$⟩ a
                          ≈⟨ Π.cong f a≈a' ⟩
                        f ⟨$⟩ a'
                          ≈⟨ f≈g a' ⟩
                        g ⟨$⟩ a'
                        ∎
     where open EqR B
    
  Equiv≈→ : IsEquivalence (_≈→_)
  Equiv≈→ = record { refl = λ {f} → isRefl {f}
                    ; sym = λ {f} {g} prf → isSym {f} {g} prf
                    ; trans = λ {f} {g} {h} p q → isTrans {f} {g} {h} p q
                    }
    where isRefl : Reflexive (_≈→_)
          isRefl {f} a = Setoid.refl B {f ⟨$⟩ a}
          isSym : Symmetric (_≈→_)
          isSym {f} {g} p a = Setoid.sym B (p a)
          isTrans : Transitive (_≈→_)
          isTrans {f} {g} {h} p q a = Setoid.trans B (p a) (q a)



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
  _⟦_⟧ₛ* ar = Carrier (HVecSet (sorts Σ) _⟦_⟧ₛ ar)


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
                      ≡to≈ : ∀ {x y : ∥ A₂ ⟦ s ⟧ₛ ∥ } → x ≡ y →
                               Setoid._≈_ (A₂ ⟦ s ⟧ₛ) x y
                      ≡to≈ refl = Setoid.refl (A₂ ⟦ s ⟧ₛ)
                      propMapMorph = 
                        begin
                          A₂ ⟦ f ⟧ₒ ⟨$⟩ (map⟿ A₁ A₂ (′ H₁ ′) $
                                              map⟿  A₀ A₁ (′ H₀ ′) as)
                            ≈⟨ ≡to≈ $ PE.cong (A₂ ⟦ f ⟧ₒ ⟨$⟩_ )
                                              (propMapV∘ as (_⟨$⟩_ ∘ ′ H₀ ′)
                                              (_⟨$⟩_ ∘ ′ H₁ ′)) ⟩
                          A₂ ⟦ f ⟧ₒ ⟨$⟩ (map⟿ A₀ A₂ comp as)
                        ∎


Total : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → Rel A ℓ₂ → Set _ 
Total _≈_ = ∀ a a' → a ≈ a'

Unique : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → Rel A ℓ₂ → Set _
Unique {A = A} _≈_ = A × Total _≈_


module Initial (Σ : Signature)
               {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} where

  open Hom
  open Algebra

  record Initial  : Set (lsuc (ℓ₄ ⊔ ℓ₃ ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      alg   : Algebra {ℓ₁} {ℓ₂} Σ
      init  : (A : Algebra {ℓ₃} {ℓ₄} Σ) → Unique (_≈ₕ_ alg A)


module TermAlgebra (Σ : Signature) where

  open Hom
  open Algebra

  data HU : (s : sorts Σ) → Set where
    term : ∀  {ar s} →  (f : ops Σ (ar ⇒ s)) → (HVec HU ar) → HU s


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
          fcong : ∀ {ar s} {f : ops Σ (ar ⇒ s)} →
                           (ts₁ ts₂ : HVec HU ar) →
                           _∼v_ {R = λ s₀ → _≡_} ts₁ ts₂ →
                           term f ts₁ ≡ term f ts₂
          fcong {f = f} ts₁ ts₂ ts₁≈ts₂ = PE.cong (term f) (≡vec ts₁ ts₂ ts₁≈ts₂)
          ∣_|ₒ  : ∀ {ar s} → ops Σ (ar ⇒ s) → (setoid ∘ HU) ✳ ar ⟶ (setoid ∘ HU) s
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


  ≡to≈ : ∀ {ℓ₁} {ℓ₂} {St : Setoid ℓ₁ ℓ₂} {x y : Carrier St} →
    x ≡ y → _≈_ St x y
  ≡to≈ {St = St} PE.refl = Setoid.refl St

  ∣H∣ : ∀ {ℓ₁ ℓ₂} → (A : Algebra {ℓ₁} {ℓ₂} Σ) → Homo ∣T∣ A
  ∣H∣ A = record { ′_′  = fun|T|ₕ
               ; cond = |T|ₕcond
               }
    where congfun : ∀ {s} {t₁ t₂ : HU s} →
                    t₁ ≡ t₂ → _≈_ (A ⟦ s ⟧ₛ) (∣h∣→A A t₁) (∣h∣→A A t₂)
          congfun {s} t₁≡t₂ = ≡to≈ {St = A ⟦ s ⟧ₛ} (PE.cong (∣h∣→A A) t₁≡t₂)
          fun|T|ₕ : ∣T∣ ⟿ A
          fun|T|ₕ s = record { _⟨$⟩_ = ∣h∣→A {s = s} A
                             ; cong  = congfun {s}
                             }
          |T|ₕcond : ∀ {ty} (f : ops Σ ty) → (homCond ∣T∣ A) fun|T|ₕ f
          |T|ₕcond {_ ⇒ s} f ⟨⟩ = ≡to≈ {St = A ⟦ s ⟧ₛ} PE.refl
          |T|ₕcond {_ ⇒ s} f (t ▹ ts) =
                   ≡to≈ {St = A ⟦ s ⟧ₛ} (PE.cong (λ ts' → A ⟦ f ⟧ₒ ⟨$⟩
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

