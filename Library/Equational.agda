module Equational where

open import UnivAlgebra
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Level renaming (zero to lzero ; suc to lsuc)
open import Relation.Binary hiding (Total)
open import Relation.Binary.PropositionalEquality as PE
open import Function as F
open import Function.Equality as FE renaming (_∘_ to _∘e_)
open import HeterogenuousVec renaming (map to mapV)

import Relation.Binary.EqReasoning as EqR


open Signature

{- Variables symbols of a signature. In the bibliography is presented as
   Ground Signature (signature with only constant symbols) -}
Vars : (Σ : Signature) → Set₁
Vars Σ = (s : sorts Σ) → Set

{- Signature extension with variables -}
_〔_〕 : (Σ : Signature) → (X : Vars Σ) → Signature
Σ 〔 X 〕 = record { sorts = sorts Σ
                   ; ops = λ { ([] , s) → ops Σ ([] , s) ⊎ X s
                             ; ty → ops Σ ty
                             }
                   }

open Algebra

{- Term Algebra of Σ (X) as Σ-Algebra -}
T_〔_〕 : (Σ : Signature) → (X : Vars Σ) →
          Algebra Σ
T Σ 〔 X 〕 = (λ s → ∣T∣ ⟦ s ⟧ₛ)
            ∥ (λ { {[]} {s} f → ∣T∣ ⟦ inj₁ f ⟧ₒ
                 ; {s₀ ∷ ar} {s} f → ∣T∣ ⟦ f ⟧ₒ })
  where open TermAlgebra (Σ 〔 X 〕)


{- Environments -}
Env : ∀ {Σ} {X : Vars Σ} {ℓ₁ ℓ₂} →
            (A : Algebra {ℓ₁} {ℓ₂} Σ) → Set ℓ₁
Env {Σ} {X} A = ∀ {s} → X s → ∥ A ⟦ s ⟧ₛ ∥


{- Extension of environments to terms -}
module EnvExt {ℓ₁ ℓ₂ : Level} {Σ} {X : Vars Σ}
              (A : Algebra {ℓ₁} {ℓ₂} Σ) where

  open TermAlgebra (Σ 〔 X 〕)

  mutual
    _↪ : (a : Env A) → {s : sorts Σ} → ∥ ∣T∣ ⟦ s ⟧ₛ ∥ → ∥ A ⟦ s ⟧ₛ ∥
    (a ↪) (term {[]} (inj₁ k) ⟨⟩) = A ⟦ k ⟧ₒ ⟨$⟩ ⟨⟩
    (a ↪) (term {[]} (inj₂ x) ⟨⟩) = a x
    (a ↪) (term {s₀ ∷ ar'} f (t ▹ ts)) = A ⟦ f ⟧ₒ ⟨$⟩ (a ↪) t ▹ (map↪ a ts)
    
    map↪ : ∀ {ar} → (a : Env A) → ∣T∣ ⟦ ar ⟧ₛ* → A ⟦ ar ⟧ₛ*
    map↪ a ⟨⟩ = ⟨⟩
    map↪ {s₀ ∷ ar'} a (t ▹ ts) = ((a ↪) t) ▹ map↪ a ts

module Subst {Σ} {X : Vars Σ} where

  Subst : Set
  Subst = Env {X = X} (T Σ 〔 X 〕)

  open TermAlgebra (Σ 〔 X 〕)

  idSubst : Subst
  idSubst = λ x → term (inj₂ x) ⟨⟩

  open EnvExt {X = X} (T Σ 〔 X 〕)

  _↪s : Subst → {s : sorts Σ} →
                  ∥ ∣T∣ ⟦ s ⟧ₛ ∥ → ∥ ∣T∣ ⟦ s ⟧ₛ ∥
  _↪s θ {s} t = (θ ↪) t
  

open Hom
open Setoid



{- Extension of the initial homomorphism to signatures with variables -}



module InitHomoExt {ℓ₁ ℓ₂ : Level}
                {Σ : Signature} {X : Vars Σ}
                (A : Algebra {ℓ₁} {ℓ₂} Σ)
                (a : Env {X = X} A) where


  --open InitTermAlg (Σ)
  open TermAlgebra (Σ 〔 X 〕) renaming (∣T∣ to ∣T∣x)
  open EnvExt {X = X} A
  open ExtEq
  open Homo

  conga↪ : ∀ {s} {t₁ t₂ : ∥ ∣T∣x ⟦ s ⟧ₛ ∥} →
                   t₁ ≡ t₂ → _≈_ (A ⟦ s ⟧ₛ) ((a ↪) t₁) ((a ↪) t₂)
  conga↪ {s} {t₁} eq = ≡to≈ (A ⟦ s ⟧ₛ) (PE.cong (a ↪) eq)

  map↪≡map : ∀ {ar} {ts : ∣T∣x ⟦ ar ⟧ₛ*} →
                   map↪ a ts ≡ mapV (λ s → (a ↪) {s}) ts
  map↪≡map {ar = []} {⟨⟩} = PE.refl
  map↪≡map {ar = s ∷ ar} {t ▹ ts} = PE.cong (λ ts' → (a ↪) t ▹ ts')
                                                 map↪≡map

  TΣX⇝A : T Σ 〔 X 〕 ⟿ A
  TΣX⇝A s = record { _⟨$⟩_ = (a ↪)
                    ; cong = conga↪ }

  {- Homomorphism condition of TΣX⇝A -}
  TΣXcond : ∀ {ty} (f : ops Σ ty) → (homCond (T Σ 〔 X 〕) A) TΣX⇝A f
  TΣXcond {.[] , s} f ⟨⟩ = Setoid.refl (A ⟦ s ⟧ₛ)
  TΣXcond {s₀ ∷ ar' , s} f (t ▹ ts) =
                ≡to≈ (A ⟦ s ⟧ₛ) (PE.cong (λ ts' → A ⟦ f ⟧ₒ ⟨$⟩
                                            (TΣX⇝A s₀ ⟨$⟩ t) ▹ ts')
                               map↪≡map)

  TΣXHom : Homo (T Σ 〔 X 〕) A
  TΣXHom = record { ′_′ = TΣX⇝A ; cond = TΣXcond }

  HomEnv : Homo (T Σ 〔 X 〕) A → Set _
  HomEnv h = (s : sorts Σ) → (x : X s) → _≈_ (A ⟦ s ⟧ₛ) ( ′ h ′ s ⟨$⟩ term (inj₂ x) ⟨⟩ ) (a x)


 
  tot : (H H' : Homo (T Σ 〔 X 〕) A) → HomEnv H → HomEnv H' → _≈ₕ_ (T Σ 〔 X 〕) A H  H'
  tot H H' he he' s (TermAlgebra.term {[]} (inj₂ v) ⟨⟩) = begin (′ H ′ s ⟨$⟩ term (inj₂ v) ⟨⟩)
                                                          ≈⟨ he s v  ⟩
                                                          a v
                                                          ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (he' s v) ⟩
                                                          ′ H' ′ s ⟨$⟩ term (inj₂ v) ⟨⟩
                                                          ∎
    where open EqR (A ⟦ s ⟧ₛ)
  tot H H' he he' s (TermAlgebra.term {[]} (inj₁ k) ⟨⟩) =
                  begin
                    ′ H ′ s ⟨$⟩ term (inj₁ k) ⟨⟩
                   ≈⟨ cond H k ⟨⟩ ⟩
                    A ⟦ k ⟧ₒ ⟨$⟩ ⟨⟩
                   ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (cond H' k ⟨⟩) ⟩
                    ′ H' ′ s ⟨$⟩ term (inj₁ k) ⟨⟩
                   ∎
    where open EqR (A ⟦ s ⟧ₛ)
  tot H H' he he' s (TermAlgebra.term {x ∷ ar} f ts) =
                  begin
                    ′ H ′ s ⟨$⟩ term f ts
                  ≈⟨ cond H f ts ⟩
                    A ⟦ f ⟧ₒ ⟨$⟩ (map⟿ (T Σ 〔 X 〕) A ′ H ′ ts)
                  ≈⟨ Π.cong (A ⟦ f ⟧ₒ) (map≈ (x ∷ ar) ts) ⟩
                    A ⟦ f ⟧ₒ ⟨$⟩ (map⟿ (T Σ 〔 X 〕) A ′ H' ′ ts)
                  ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (cond H' f ts) ⟩ 
                    ′ H' ′ s ⟨$⟩ term f ts
                  ∎
    where open EqR (A ⟦ s ⟧ₛ)
          map≈ : (ar : Arity Σ) → (ts : HVec (HU) ar) →
                 _∼v_ {R = _≈_ ∘ (_⟦_⟧ₛ A)} (mapV (_⟨$⟩_ ∘ ′ H ′) ts) (mapV (_⟨$⟩_ ∘ ′ H' ′) ts)
          map≈ [] ⟨⟩ = ∼⟨⟩
          map≈ (s ∷ ar) (t ▹ ts) = ∼▹ (tot H H' he he' s t)
                                      (map≈ ar ts)



open TermAlgebra


{- Equations -}

record Equation (Σ : Signature) (X : Vars Σ) (s : sorts Σ) : Set where
  constructor ⋀_≈_if「_」_
  field
    left  : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥
    right : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥
    carty : Arity Σ
    cond : HVec (λ s' → ∥ ∣T∣ (Σ 〔 X 〕) ⟦ s' ⟧ₛ ∥) carty ×
           HVec (λ s' → ∥ ∣T∣ (Σ 〔 X 〕) ⟦ s' ⟧ₛ ∥) carty


{- Unconditional equation -}
⋀_≈_ : ∀ {Σ X s} → (t t' : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥) → Equation Σ X s
⋀ t ≈ t' = ⋀ t ≈ t' if「 [] 」 (⟨⟩ , ⟨⟩)


{- Explicar la decisión de indexar la teoría en el conjunto de variables -}


Theory : (Σ : Signature) → (X : Vars Σ) → (ar : Arity Σ) → Set
Theory Σ X ar = HVec (Equation Σ X) ar



-- Satisfactibility
{-
Discusión: En las reglas de substitución y reemplazo, hay dos conjuntos de variables
           X e Y, para que tenga sentido debe haber una inclusión. Aquí estamos
           indexando todas las definiciones en el conjunto de variables. No debería
           haber problemas ya que en todo caso la cuantificación habla de variables
           que pueden no ocurrir en los términos.
           Esto que dije antes NO es cierto. Pero yo estoy usando un solo conjunto de
           variables. No debería ser un problema ya que siempre puedo expresar las ecuaciones
           con el conjunto de variables más grande posible.
-}

_⊨_ : ∀ {ℓ₁ ℓ₂ Σ X} {s : sorts Σ} →
        (A : Algebra {ℓ₁} {ℓ₂} Σ) → Equation Σ X s → Set (ℓ₂ Level.⊔ ℓ₁)
_⊨_ {s = s} A (⋀ t ≈ t' if「 _ 」 (us , us')) =
    (θ : Env A) →
    _∼v_ {R = λ sᵢ uᵢ uᵢ' → _≈_ (A ⟦ sᵢ ⟧ₛ) ((θ ↪) uᵢ) ((θ ↪) uᵢ')} us us' →
    (_≈_ (A ⟦ s ⟧ₛ)) ((θ ↪) t) ((θ ↪) t')
    
  where open EnvExt A

record  ⊨T {ℓ₁ ℓ₂ : Level} {Σ X} {ar : Arity Σ} (E : Theory Σ X ar)
                         (A : Algebra {ℓ₁} {ℓ₂} Σ) : Set (ℓ₂ Level.⊔ ℓ₁)  where
  field
    satAll : ∀ {s} {e : Equation Σ X s} → e ∈ E → A ⊨ e


open ⊨T

{- Quisiera poder cuantificar universalmente sobre todas las álgebras
   de una signatura, pero para ello debería poder cuantificar sobre todos
   los niveles, y no puedo hacerlo en Agda. Debo dar una definición de ⊨All
   para cada par de niveles -}
⊨All : ∀ {ℓ₁ ℓ₂ Σ X} {ar : Arity Σ} {s : sorts Σ} → (E : Theory Σ X ar) →
               (e : Equation Σ X s) → Set (lsuc ℓ₂ Level.⊔ lsuc ℓ₁)
⊨All {ℓ₁} {ℓ₂} {Σ} E e = (A : Algebra {ℓ₁} {ℓ₂} Σ) → ⊨T {ℓ₁} {ℓ₂} E A → A ⊨ e


open Subst

{- Provability -}
data _⊢_ {Σ X}
            {ar : Arity Σ} (E : Theory Σ X ar) :
          {s : sorts Σ} → Equation Σ X s → Set where
  prefl : ∀ {s} {t : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥} → E ⊢ (⋀ t ≈ t)
  psym : ∀ {s} {t t' : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥} → E ⊢ (⋀ t ≈ t') →
                                                  E ⊢ (⋀ t' ≈ t)
  ptrans : ∀ {s} {t₀ t₁ t₂ : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥} →
                 E ⊢ (⋀ t₀ ≈ t₁) → E ⊢ (⋀ t₁ ≈ t₂) → E ⊢ (⋀ t₀ ≈ t₂)
  psubst : ∀ {s} {ar} {us us' : HVec (λ s' → ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) ar}
           {t t' : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥} →
           (⋀ t ≈ t' if「 ar 」 (us , us')) ∈ E →
           (σ : Subst) →
           _∼v_ {R = λ sᵢ uᵢ uᵢ' → E ⊢ (⋀ (σ ↪s) uᵢ ≈ (σ ↪s) uᵢ')} us us' →
           E ⊢ (⋀ (σ ↪s) t ≈ (σ ↪s) t')
  preemp : ∀ {ar'} {s} {ts ts' : HVec (λ s' → ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) ar'} →
             _∼v_ {R = λ sᵢ tᵢ tᵢ' → E ⊢ (⋀ tᵢ ≈ tᵢ')} ts ts' →
             (f : ops (Σ 〔 X 〕) (ar' , s)) → E ⊢ (⋀ term f ts ≈ term f ts') 

open EnvExt


{- Composition of an environment with a substitution -}
EnvSubst : ∀ {Σ X ℓ₁ ℓ₂} {A : Algebra {ℓ₁} {ℓ₂} Σ} →
             (σ : Subst) → (θ : Env {X = X} A) → Env A
EnvSubst {A = A} σ θ x = (A ↪) θ (σ x)


mutual
  ∘subst : ∀ {Σ X ℓ₁ ℓ₂ s} {A : Algebra {ℓ₁} {ℓ₂} Σ} →
                  (σ : Subst) → (θ : Env A) → (t₀ : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥) →
                  (A ⟦ s ⟧ₛ ≈ (A ↪) (EnvSubst {A = A} σ θ) t₀) ((A ↪) θ ((σ ↪s) t₀))
  ∘subst {A = A} σ θ (term {[]} {s} (inj₁ x) ⟨⟩) = Setoid.refl (A ⟦ s ⟧ₛ)
  ∘subst {A = A} σ θ (term {[]} {s} (inj₂ y) ⟨⟩) = Setoid.refl (A ⟦ s ⟧ₛ)
  ∘subst {A = A} σ θ (term {s₀ ∷ ar} {s} f (t₀ ▹ ts)) =
                                         Π.cong (A ⟦ f ⟧ₒ) (∼▹ (∘subst {A = A} σ θ t₀)
                                                              (map∘subst σ θ ts))

  map∘subst : ∀ {Σ X ℓ₁ ℓ₂ ar} {A : Algebra {ℓ₁} {ℓ₂} Σ} →
                (σ : Subst) → (θ : Env A) → (ts : HVec (λ s' → ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) ar) →
                _∼v_ {R = _≈_ ∘ _⟦_⟧ₛ A} (map↪ A (EnvSubst {A = A} σ θ) ts)
                                        (map↪ A θ (map↪ T Σ 〔 X 〕 σ ts))
  map∘subst σ θ ⟨⟩ = ∼⟨⟩
  map∘subst {A = A} σ θ (t ▹ ts) = ∼▹ (∘subst {A = A} σ θ t) (map∘subst σ θ ts)


correctness : ∀ {ℓ₁ ℓ₂ Σ X} {ar : Arity Σ} {s : sorts Σ} {E : Theory Σ X ar}
                {e : Equation Σ X s} → E ⊢ e → ⊨All {ℓ₁} {ℓ₂} E e
correctness {X = X} {ar} {s} prefl = λ A _ _ _ → Setoid.refl (A ⟦ s ⟧ₛ)
correctness {X = X} {ar} {s} {E} (psym pe) = 
                 λ { A sall θ ∼⟨⟩ → Setoid.sym (A ⟦ s ⟧ₛ)
                                    (correctness pe A sall θ ∼⟨⟩) }
correctness {X = X} {ar} {s} {E} (ptrans pe₀ pe₁) =
                 λ { A x θ ∼⟨⟩ → Setoid.trans (A ⟦ s ⟧ₛ)
                                 (correctness pe₀ A x θ ∼⟨⟩)
                                 (correctness pe₁ A x θ ∼⟨⟩) }
correctness {Σ = Σ} {X} {ar} {s} {E}
            (psubst {us = us} {us'} {t} {t'} econd σ ⊢us≈us') A sall θ ∼⟨⟩ = A⊨econd
  where θσ : Env A
        θσ = EnvSubst {A = A} σ θ
        iHus : ∀ {ar₀} {us₀ us₀' : HVec (λ s' → ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) ar₀} →
               (θ' : Env A) → 
               _∼v_ {R = λ sᵢ uᵢ uᵢ' → E ⊢ (⋀ (σ ↪s) uᵢ ≈ (σ ↪s) uᵢ')} us₀ us₀' →
               _∼v_ {R = λ sᵢ uᵢ uᵢ' → (A ⟦ sᵢ ⟧ₛ ≈ (A ↪) θ' ((σ ↪s) uᵢ))
                                                 ((A ↪) θ' ((σ ↪s) uᵢ'))} us₀ us₀'
        iHus θ' ∼⟨⟩ = ∼⟨⟩
        iHus θ' (∼▹ {s₀} {ar₀} {u₁} {u₂} ⊢u₁≈u₂ p) = ∼▹ (correctness ⊢u₁≈u₂ A sall θ' ∼⟨⟩)
                                                       (iHus θ' p)
        θσ↪≈θ↪∘σ↪ : ∀ {s'} → (t₀ : ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) →
                        (A ⟦ s' ⟧ₛ ≈ (A ↪) θσ t₀) ((A ↪) θ ((σ ↪s) t₀))
        θσ↪≈θ↪∘σ↪ = ∘subst {A = A} σ θ
        A⊨econd : ((A ⟦ s ⟧ₛ) ≈ (A ↪) θ ((σ ↪s) t))
                               ((A ↪) θ ((σ ↪s) t'))
        A⊨econd = begin
                   (A ↪) θ ((σ ↪s) t)
                     ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (θσ↪≈θ↪∘σ↪ t)⟩
                   (A ↪) θσ t
                     ≈⟨ satAll sall econd θσ (map∼v (λ {s₀} {uᵢ} {uᵢ'} x →
                                             Setoid.trans (A ⟦ s₀ ⟧ₛ) (θσ↪≈θ↪∘σ↪ uᵢ)
                                             (Setoid.trans (A ⟦ s₀ ⟧ₛ) x (Setoid.sym (A ⟦ s₀ ⟧ₛ) (θσ↪≈θ↪∘σ↪ uᵢ'))))
                                             (iHus θ ⊢us≈us')) ⟩
                   (A ↪) θσ t'
                     ≈⟨ θσ↪≈θ↪∘σ↪ t' ⟩
                   (A ↪) θ ((σ ↪s) t')
                   ∎
          where open EqR (A ⟦ s ⟧ₛ)
correctness {s = s} {E} (preemp {[]} ∼⟨⟩ f) = λ { A x θ ∼⟨⟩ → Setoid.refl (A ⟦ s ⟧ₛ) }
correctness {ℓ₁} {ℓ₂} {Σ} {X} {ar} {s} {E}
            (preemp {x ∷ ar'} {.s} {ts} {ts'} ⊢ts≈ts' f) A sall θ ∼⟨⟩ =
                begin
                   (A ↪) θ (term f ts)
                 ≈⟨ TΣXcond f ts ⟩
                   A ⟦ f ⟧ₒ ⟨$⟩ map⟿ (T Σ 〔 X 〕) A TΣX⇝A ts
                 ≈⟨ Π.cong (A ⟦ f ⟧ₒ) (map≈ (iHts ⊢ts≈ts')) ⟩
                   A ⟦ f ⟧ₒ ⟨$⟩ map⟿ (T Σ 〔 X 〕) A TΣX⇝A ts'
                 ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (TΣXcond f ts') ⟩
                   (A ↪) θ (term f ts')
                ∎
                
  where open EqR (A ⟦ s ⟧ₛ)
        open InitHomoExt A θ
        iHts : ∀ {ar₀} {ts₀ ts₀' : HVec (λ s' → ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) ar₀} →
               _∼v_ {R = λ sᵢ tᵢ tᵢ' → E ⊢ (⋀ tᵢ ≈ tᵢ')} ts₀ ts₀' →
               _∼v_ {R = λ sᵢ tᵢ tᵢ' → (A ⟦ sᵢ ⟧ₛ ≈ (A ↪) θ tᵢ)
                                                 ((A ↪) θ tᵢ')} ts₀ ts₀'
        iHts {[]} {⟨⟩} ∼⟨⟩ = ∼⟨⟩
        iHts {s₀ ∷ ar₀} {t₀ ▹ ts₀} {t₀' ▹ ts₀'} (∼▹ ⊢t₀≈t₀' ⊢ts₀≈ts₀') =
                                    ∼▹ (ih ⊢t₀≈t₀' A sall θ ∼⟨⟩) (iHts ⊢ts₀≈ts₀')
          where ih : ∀ {s' : sorts Σ} {tᵢ tᵢ' : ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥} →
                       E ⊢ (⋀ tᵢ ≈ tᵢ') → ⊨All E (⋀ tᵢ ≈ tᵢ')
                ih {s'} {tᵢ} {tᵢ'} peq = correctness peq
        map≈ : ∀ {ar'} {ts₀ ts₀' : HVec (λ s' → ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) ar'} →
               (p : _∼v_ {R = λ sᵢ tᵢ tᵢ' → (A ⟦ sᵢ ⟧ₛ ≈ (A ↪) θ tᵢ)
                                                 ((A ↪) θ tᵢ')} ts₀ ts₀') →
               _∼v_ {R = λ s₀ → _≈_ (A ⟦ s₀ ⟧ₛ)}
               (map⟿ (T Σ 〔 X 〕) A TΣX⇝A ts₀) (map⟿ (T Σ 〔 X 〕) A TΣX⇝A ts₀')
        map≈ {[]} ∼⟨⟩ = ∼⟨⟩
        map≈ {i ∷ is} {t₀ ▹ ts₀} {t₀' ▹ ts₀'} (∼▹ p₀ p) = ∼▹ p₀ (map≈ p)


-- Completeness
⊢R : ∀ {Σ X ar} → (E : Theory Σ X ar) → (s : sorts Σ) →
       Rel (∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥) (Level.zero)
⊢R E s t t' = E ⊢ (⋀ t ≈ t') 

⊢REquiv : ∀ {Σ X ar} → (E : Theory Σ X ar) → (s : sorts Σ) →
          IsEquivalence (⊢R E s)
⊢REquiv E s = record { refl = prefl
                     ; sym = psym
                     ; trans = ptrans
                     }

⊢RSetoid : ∀ {Σ X ar} → (E : Theory Σ X ar) → (s : sorts Σ) → Setoid (Level.zero) (Level.zero)
⊢RSetoid {Σ} {X} {ar} E s = record { Carrier = ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥
                                   ; _≈_ = ⊢R E s
                                   ; isEquivalence = ⊢REquiv E s
                                   }

⊢Cong : ∀ {Σ X ar} → (E : Theory Σ X ar) → Congruence (T Σ 〔 X 〕)
⊢Cong {Σ} {X} E = record { rel = ⊢R E
               ; welldef = pwdef
               ; cequiv = ⊢REquiv E
               ; csubst = pcsubst }
  where pwdef : ∀ {s} {t₀ t₀' t₁ t₁'} → t₀ ≡ t₀' → t₁ ≡ t₁' → ⊢R E s t₀ t₁ →
                                         ⊢R E s t₀' t₁'
        pwdef {s} {t₀} {.t₀} {t₁} {.t₁} PE.refl PE.refl ⊢t₀≈t₁ = ⊢t₀≈t₁
        pcsubst : ∀ {ar} {s} → (f : ops Σ (ar , s)) →
                    _∼v_ =[ _⟨$⟩_ (T Σ 〔 X 〕 ⟦ f ⟧ₒ) ]⇒ ⊢R E s
        pcsubst {[]} f ∼⟨⟩ = prefl
        pcsubst {s₀ ∷ ar} {s} f {ts} {ts'} ⊢ts≈ts' = preemp ⊢ts≈ts' f
        
⊢Quot : ∀ {Σ X ar} → (E : Theory Σ X ar) → Algebra {Level.zero} { (Level.zero)} Σ
⊢Quot {Σ} {X} E = Quotient T Σ 〔 X 〕 (⊢Cong E)


⊢Quot⊨E : ∀ {Σ X ar} → (E : Theory Σ X ar) → ⊨T {lzero} {lzero} E (⊢Quot E)
⊢Quot⊨E {Σ} {X} {ar} E = record { satAll = sall }
  where
    mutual
        thm : ∀ {s} {t} {θ : Subst} → ((T Σ 〔 X 〕 ⟦ s ⟧ₛ) ≈ (θ ↪s) t) ((⊢Quot E ↪) θ t)
        thm {t = term (inj₁ x) ⟨⟩} {θ} = _≡_.refl
        thm {t = term (inj₂ y) ⟨⟩} {θ} = _≡_.refl
        thm {t = term f (t ▹ ts)} {θ} = PE.cong (term f) (thm' {ts = t ▹ ts} {θ} )

        thm' : ∀ {ar'} {ts : HVec (HU (Σ 〔 X 〕)) ar' } {θ : Subst} → map↪ T Σ 〔 X 〕 θ ts ≡ map↪ (⊢Quot E) θ ts
        thm' {ts = ⟨⟩} {θ} = _≡_.refl
        thm' {ts = v ▹ ts} {θ} = cong₂ _▹_ (thm {t = v} {θ}) (thm' {ts = ts} {θ})


    sall : ∀ {s} {e : Equation Σ X s} → _∈_ {is = ar} e E → (⊢Quot E) ⊨ e
    sall {s} {e = ⋀ t ≈ t' if「 ar' 」 ( us , us') } e∈E θ us~us' = Congruence.welldef (⊢Cong E) (thm {s} {t} {θ}) (thm {s} {t'} {θ}) equi 
          where open EqR (⊢RSetoid E s)
                equi : E ⊢ (⋀ (θ ↪s) t ≈ (θ ↪s) t')
                equi = psubst {Σ} {X} {ar} {E} {s} {ar'} {us} {us'} {t} {t'} e∈E θ
                  (map∼v (λ {i} {ua} {ub} → Congruence.welldef (⊢Cong E)
                                (Setoid.sym (_⟦_⟧ₛ T Σ 〔 X 〕 i) (thm {t = ua} {θ}))
                                (Setoid.sym (_⟦_⟧ₛ T Σ 〔 X 〕 i) (thm {t = ub} {θ}))) us~us')


complete : ∀ {Σ X} {ar : Arity Σ} {s : sorts Σ} {E : Theory Σ X ar}
             {t t' : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥ } →
             ⊨All {Level.zero} {Level.zero} E (⋀ t ≈ t') → E ⊢ (⋀ t ≈ t')
complete {Σ} {X} {ar} {s} {E} {t} {t'} sall = begin t
                  ≈⟨ ≡to≈ (⊢RSetoid E s) (PE.sym (idSubst≡ t)) ⟩
                  ((λ x → term (inj₂ x) ⟨⟩) ↪s) t
                  ≈⟨ Congruence.welldef (⊢Cong E ) (Setoid.sym ((_⟦_⟧ₛ T Σ 〔 X 〕 s)) (thm {t = t} {λ x → term (inj₂ x) ⟨⟩}))
                                                   ((Setoid.sym ((_⟦_⟧ₛ T Σ 〔 X 〕 s)) (thm {t = t'} {λ x → term (inj₂ x) ⟨⟩}))) (sall (⊢Quot E) (⊢Quot⊨E E) (λ x → term (inj₂ x) ⟨⟩) ∼⟨⟩) ⟩
                  ((λ x → term (inj₂ x) ⟨⟩) ↪s) t'
                  ≈⟨ ≡to≈ (⊢RSetoid E s) ((idSubst≡ t')) ⟩
                  t' ∎
  where
   open EqR (⊢RSetoid E s)
   mutual
        thm : ∀ {s} {t} {θ : Subst} → ((T Σ 〔 X 〕 ⟦ s ⟧ₛ) ≈ (θ ↪s) t) ((⊢Quot E ↪) θ t)
        thm {t = term (inj₁ x) ⟨⟩} {θ} = _≡_.refl
        thm {t = term (inj₂ y) ⟨⟩} {θ} = _≡_.refl
        thm {t = term f (t ▹ ts)} {θ} = PE.cong (term f) (thm' {ts = t ▹ ts} {θ} )

        thm' : ∀ {ar'} {ts : HVec (HU (Σ 〔 X 〕)) ar' } {θ : Subst} → map↪ T Σ 〔 X 〕 θ ts ≡ map↪ (⊢Quot E) θ ts
        thm' {ts = ⟨⟩} {θ} = _≡_.refl
        thm' {ts = v ▹ ts} {θ} = cong₂ _▹_ (thm {t = v} {θ}) (thm' {ts = ts} {θ})

   mutual
    idSubst≡ : ∀ {s} → (t : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥) →
                 ((λ x → term (inj₂ x) ⟨⟩) ↪s) t ≡ t
    idSubst≡ (term {[]} (inj₁ x) ⟨⟩) = _≡_.refl
    idSubst≡ (term {[]} (inj₂ y) ⟨⟩) = _≡_.refl
    idSubst≡ (term {s₀ ∷ ar'} f (t ▹ ts)) = cong₂ (λ t₀ ts₀ → term f (t₀ ▹ ts₀))
                                                  (idSubst≡ t) (map↪id ts)

    map↪id : ∀ {ar'} → (ts : HVec (λ s' → ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) ar') → (map↪ T Σ 〔 X 〕 (λ x → term (inj₂ x) ⟨⟩) ts) ≡ ts
    map↪id ⟨⟩ = _≡_.refl
    map↪id (t ▹ ts) = cong₂ (λ t₀ ts₀ → t₀ ▹ ts₀)
                            (idSubst≡ t) (map↪id ts)

module Rewrite (Σ : Signature) (X : Vars Σ) where

  _matches_ : ∀ {s} → (p t : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥) → Set
  p matches t = Σ[ σ ∈ Subst ] (σ ↪s) p ≡ t

  mutual
    FV : ∀ {s} → (t : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥) → Σ[ ar ∈ Arity Σ ] HVec (λ s₀ → X s₀) ar
    FV (term {[]} (inj₁ x) ⟨⟩) = [] , ⟨⟩
    FV (term {[]} {s} (inj₂ y) ⟨⟩) = s ∷ [] , y ▹ ⟨⟩
    FV (term {s₀ ∷ ar} f (t ▹ ts)) = ar₀ ++ ar' , (vs₀ ++v vs)
      where ar' : Arity Σ
            ar' = proj₁ (mapFV ts)
            vs : HVec X ar'
            vs = proj₂ (mapFV ts)
            ar₀ : Arity Σ
            ar₀ = proj₁ (FV t)
            vs₀ : HVec X ar₀
            vs₀ = proj₂ (FV t)

    mapFV : ∀ {ar} → (ts : T Σ 〔 X 〕 ⟦ ar ⟧ₛ*) → Σ[ ar ∈ Arity Σ ] HVec X ar
    mapFV ⟨⟩ = [] , ⟨⟩
    mapFV (t ▹ ts) = ar₀ ++ ar' , (vs₀ ++v vs)
      where ar' : Arity Σ
            ar' = proj₁ (mapFV ts)
            vs : HVec X ar'
            vs = proj₂ (mapFV ts)
            ar₀ : Arity Σ
            ar₀ = proj₁ (FV t)
            vs₀ : HVec X ar₀
            vs₀ = proj₂ (FV t)

  {- Rewrite Rule -}
  record Rule (s : sorts Σ) : Set where
    field
      l : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥
      r : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥
      rcond : ∀ {s₀} {x : X s₀} → x ∈ (proj₂ (FV r)) → x ∈ (proj₂ (FV l))

  {- Term Rewriting System -}
  TRS : (ar : Arity Σ) → Set
  TRS ar = HVec Rule ar


module ProvSetoid {Σ : Signature} {X : Vars Σ}
                  {ar : Arity Σ} 
                  (Th : Theory Σ X ar) where


  ProvSetoid : (s : sorts Σ) → Setoid _ _
  ProvSetoid s = record { Carrier = ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥
                        ; _≈_ = λ t t' → Th ⊢ (⋀ t ≈ t')
                        ; isEquivalence = record { refl = prefl
                                                 ; sym = psym
                                                 ; trans = ptrans } }

  

-- Theory implication
_⇒T_ : ∀ {Σ X ar ar'} → Theory Σ X ar → Theory Σ X ar' → Set
_⇒T_ {Σ} {X} T₁ T₂ = ∀ {s} {ax : Equation Σ X s} → ax ∈ T₂ → T₁ ⊢ ax


⊨T⇒ : ∀ {ℓ₁ ℓ₂ Σ X ar ar'} → (T₁ : Theory Σ X ar) (T₂ : Theory Σ X ar')
        (p⇒ : T₁ ⇒T T₂) → (A : Algebra {ℓ₁} {ℓ₂} Σ) → ⊨T T₁ A → ⊨T T₂ A
⊨T⇒ T₁ T₂ p⇒ A record { satAll = satAll } =
                        record { satAll = λ ax θ ~cond →
                        correctness (p⇒ ax) A (record { satAll = satAll }) θ ~cond }

{-
open import Relation.Unary hiding (_∈_)
Class : ∀ {ℓ₁ ℓ₂ ℓ₃} → (Σ : Signature) → Set _
Class {ℓ₁} {ℓ₂} {ℓ₃} Σ = Pred (Algebra {ℓ₁} {ℓ₂} Σ) ℓ₃

⊨Class : ∀ {ℓ₁ ℓ₂ Σ X} {ar : Arity Σ} → (E : Theory Σ X ar) →
           Class {ℓ₁} {ℓ₂} Σ
⊨Class E = λ A → ⊨T E A

HSP : ∀ {ℓ₁ ℓ₂ ℓ₃ Σ} → Pred (Class Σ) _
HSP = {!!}

Birkhoff₁ : ∀ {Σ X} {ar : Arity Σ} → (E : Theory Σ X ar) →
              HSP (⊨Class E)
Birkhoff₁ = {!!}

Birkhoff₂ : ∀ {Σ X} {ar : Arity Σ} → (C : Class Σ) →
              (HSP C) → Σ[ E ∈ Theory Σ X ar ] ((A : Algebra Σ) → C A → ⊨Class E A)
Birkhoff₂ C hspC = {!!}
-}



