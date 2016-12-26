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
            (A : Algebra {ℓ₁} {ℓ₂} Σ) → Set _
Env {Σ} {X} A = (s : sorts Σ) → X s → ∥ A ⟦ s ⟧ₛ ∥


{- Extension of environments -}
module EnvExt {ℓ₁ ℓ₂ : Level} {Σ} {X : Vars Σ}
              (A : Algebra {ℓ₁} {ℓ₂} Σ) where

  open TermAlgebra (Σ 〔 X 〕)

  mutual
    _↪ : (a : Env A) → (s : sorts Σ) → ∥ ∣T∣ ⟦ s ⟧ₛ ∥ → ∥ A ⟦ s ⟧ₛ ∥
    (a ↪) s (term {[]} (inj₁ k) ⟨⟩) = A ⟦ k ⟧ₒ ⟨$⟩ ⟨⟩
    (a ↪) s (term {[]} (inj₂ x) ⟨⟩) = a s x
    (a ↪) s (term {s₀ ∷ ar'} f (t ▹ ts)) = A ⟦ f ⟧ₒ ⟨$⟩ (a ↪) s₀ t ▹ (map↪ a ts)
    
    map↪ : ∀ {ar} → (a : Env A) → ∣T∣ ⟦ ar ⟧ₛ* → A ⟦ ar ⟧ₛ*
    map↪ a ⟨⟩ = ⟨⟩
    map↪ {s₀ ∷ ar'} a (t ▹ ts) = ((a ↪) s₀ t) ▹ map↪ a ts

module Subst {Σ} {X : Vars Σ} where

  Subst : Set
  Subst = Env {X = X} (T Σ 〔 X 〕)

  open TermAlgebra (Σ 〔 X 〕)

  idSubst : Subst
  idSubst = λ s x → term (inj₂ x) ⟨⟩

  open EnvExt {X = X} (T Σ 〔 X 〕)

  _↪s : Subst → {s : sorts Σ} →
                  ∥ ∣T∣ ⟦ s ⟧ₛ ∥ → ∥ ∣T∣ ⟦ s ⟧ₛ ∥
  _↪s θ {s} t = (θ ↪) s t
  
  mutual
    idSubst≡ : ∀ {s} → (t : ∥ ∣T∣ ⟦ s ⟧ₛ ∥) →
                 (idSubst ↪s) t ≡ t
    idSubst≡ (term {[]} (inj₁ x) ⟨⟩) = refl
    idSubst≡ (term {[]} (inj₂ y) ⟨⟩) = refl
    idSubst≡ (term {s₀ ∷ ar'} f (t ▹ ts)) = cong₂ (λ t₀ ts₀ → term f (t₀ ▹ ts₀))
                                                  (idSubst≡ t) (map↪id ts)

    map↪id : ∀ {ar} → (ts : ∣T∣ ⟦ ar ⟧ₛ*) →
                       map↪ idSubst ts ≡ ts
    map↪id ⟨⟩ = refl
    map↪id (t ▹ ts) = cong₂ (λ t₀ ts₀ → t₀ ▹ ts₀)
                            (idSubst≡ t) (map↪id ts)


{-
{- Substitution -}
Subst : ∀ {Σ} → (X : Vars Σ) → Set _
Subst {Σ} X = Env {X = X} (T Σ 〔 X 〕)


{- Identity substitution -}
idSubst : ∀ {Σ} → (X : Vars Σ) → Subst {Σ} X
idSubst {Σ} X = λ s x → term (inj₂ x) ⟨⟩
  where open TermAlgebra (Σ 〔 X 〕)


{- Application of a substitution on a term -}
_↪s : ∀ {Σ X} → Subst X → {s : sorts Σ} → ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥ →
                                             ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥
_↪s {Σ} {X} θ {s} t = (θ ↪) s t
  where open EnvExt (T Σ 〔 X 〕)


mutual
  idSubst≡ : ∀ {Σ X s} → (t : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥) →
               (idSubst X ↪s) t ≡ t
  idSubst≡ (TermAlgebra.term {[]} (inj₁ x) ⟨⟩) = refl
  idSubst≡ (TermAlgebra.term {[]} (inj₂ y) ⟨⟩) = refl
  idSubst≡ {Σ} {X} (TermAlgebra.term {i ∷ is} f (v ▹ vs)) = {!!}
    where open EnvExt (T Σ 〔 X 〕)

  map↪ : ∀ {X ar} → (ts : T Σ 〔 X 〕 ⟦ ar ⟧ₛ*) →
                     map↪ (idSubst X ↪s) ts ≡ ts
  map↪ ts = ?
    where open EnvExt (T Σ 〔 X 〕)
-}


open Hom
open Setoid


{- There exists an unique homomorphism from T Σ ( X ) to any other
   Σ-Algebra, for each environment -}


{- Freeness property -}
module Freeness {ℓ₁ ℓ₂ : Level}
                {Σ : Signature} {X : Vars Σ}
                (A : Algebra {ℓ₁} {ℓ₂} Σ)
                (a : Env {X = X} A) where


  open InitTermAlg (Σ)
  open TermAlgebra (Σ 〔 X 〕)
  open EnvExt {X = X} A
  open ExtEq
  open Homo
                                                                   
  conga↪ : ∀ {s} {t₁ t₂ : ∥ ∣T∣ ⟦ s ⟧ₛ ∥} →
                   t₁ ≡ t₂ → _≈_ (A ⟦ s ⟧ₛ) ((a ↪) s t₁) ((a ↪) s t₂)
  conga↪ {s} {t₁} eq = ≡to≈ (A ⟦ s ⟧ₛ) (PE.cong ((a ↪) s) eq)

  map↪≡map : ∀ {ar} {ts : ∣T∣ ⟦ ar ⟧ₛ*} →
                   map↪ a ts ≡ mapV (a ↪) ts
  map↪≡map {ar = []} {⟨⟩} = PE.refl
  map↪≡map {ar = s ∷ ar} {t ▹ ts} = PE.cong (λ ts' → (a ↪) s t ▹ ts')
                                                 map↪≡map

  TΣX⇝A : T Σ 〔 X 〕 ⟿ A
  TΣX⇝A s = record { _⟨$⟩_ = (a ↪) s
                    ; cong = conga↪ }

  {- Homomorphism condition of TΣX⇝A -}
  TΣXcond : ∀ {ty} (f : ops Σ ty) → (homCond (T Σ 〔 X 〕) A) TΣX⇝A f
  TΣXcond {.[] , s} f ⟨⟩ = Setoid.refl (A ⟦ s ⟧ₛ)
  TΣXcond {s₀ ∷ ar' , s} f (t ▹ ts) =
                ≡to≈ (A ⟦ s ⟧ₛ) (PE.cong (λ ts' → A ⟦ f ⟧ₒ ⟨$⟩
                                            (TΣX⇝A s₀ ⟨$⟩ t) ▹ ts')
                               map↪≡map)
{-
  uniqueTΣX : Total (T Σ 〔 X 〕 ≈ₕ A)
  uniqueTΣX H₁ H₂ s (TermAlgebra.term {[]} (inj₂ x) ⟨⟩) =
            begin
              ′ H₁ ′ s ⟨$⟩ term (inj₂ x) ⟨⟩
            ≈⟨ {!!} ⟩
              a s x
            ≈⟨ {!!} ⟩
              ′ H₂ ′ s ⟨$⟩ term (inj₂ x) ⟨⟩
            ∎
    where open EqR (A ⟦ s ⟧ₛ)
  uniqueTΣX H₁ H₂ s (TermAlgebra.term {[]} (inj₁ k) ⟨⟩) =
            begin
              ′ H₁ ′ s ⟨$⟩ term (inj₁ k) ⟨⟩
            ≈⟨ cond H₁ k ⟨⟩ ⟩
              A ⟦ k ⟧ₒ ⟨$⟩ ⟨⟩
            ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (cond H₂ k ⟨⟩) ⟩
              ′ H₂ ′ s ⟨$⟩ term (inj₁ k) ⟨⟩
            ∎
    where open EqR (A ⟦ s ⟧ₛ)
  uniqueTΣX H₁ H₂ s (TermAlgebra.term {s₀ ∷ ar} f ts) = {!!}


  freeness : Unique (_≈ₕ_ (T Σ 〔 X 〕) A)
  freeness = (record { ′_′ = TΣX⇝A ; cond = TΣXcond })
           , uniqueTΣX
-}

open TermAlgebra


{- Equations -}

record Equation (Σ : Signature) (X : Vars Σ) (s : sorts Σ) : Set₁ where
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


Theory : (Σ : Signature) → (X : Vars Σ) → (ar : Arity Σ) → Set₁
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
        (A : Algebra {ℓ₁} {ℓ₂} Σ) → Equation Σ X s → Set _
_⊨_ {s = s} A (⋀ left ≈ right if「 carty 」 cond) =
    (θ : Env A) →
    _∼v_ {R = λ sᵢ uᵢ uᵢ' → _≈_ (A ⟦ sᵢ ⟧ₛ) ((θ ↪) sᵢ uᵢ) ((θ ↪) sᵢ uᵢ')}
         (proj₁ cond) (proj₂ cond) →
    (_≈_ (A ⟦ s ⟧ₛ)) ((θ ↪) s left)
                    ((θ ↪) s right)
    
  where open EnvExt A


record ⊨T {ℓ₁ ℓ₂ : Level} {Σ X} {ar : Arity Σ} (E : Theory Σ X ar)
                         (A : Algebra {ℓ₁} {ℓ₂} Σ) : Set₁  where
  field
    satAll : ∀ {s} {e : Equation Σ X s} → e ∈ E → A ⊨ e


open ⊨T

{- Quisiera poder cuantificar universalmente sobre todas las álgebras
   de una signatura, pero para ello debería poder cuantificar sobre todos
   los niveles, y no puedo hacerlo en Agda. Debo dar una definición de ⊨All
   para cada par de niveles -}
⊨All : ∀ {ℓ₁ ℓ₂ Σ X} {ar : Arity Σ} {s : sorts Σ} → (E : Theory Σ X ar) →
               (e : Equation Σ X s) → Set _
⊨All {ℓ₁} {ℓ₂} {Σ} E e = (A : Algebra {ℓ₁} {ℓ₂} Σ) → ⊨T E A → A ⊨ e


open Subst

{- Provability -}
data _⊢_ {Σ X}
            {ar : Arity Σ} (E : HVec (Equation Σ X) ar) :
          {s : sorts Σ} → Equation Σ X s → Set₁ where
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
EnvSubst {A = A} σ θ s x = (A ↪) θ s (σ s x)


mutual
  ∘subst : ∀ {Σ X ℓ₁ ℓ₂ s} {A : Algebra {ℓ₁} {ℓ₂} Σ} →
                  (σ : Subst) → (θ : Env A) → (t₀ : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥) →
                  (A ⟦ s ⟧ₛ ≈ (A ↪) (EnvSubst {A = A} σ θ) s t₀) ((A ↪) θ s ((σ ↪s) t₀))
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
               _∼v_ {R = λ sᵢ uᵢ uᵢ' → (A ⟦ sᵢ ⟧ₛ ≈ (A ↪) θ' sᵢ ((σ ↪s) uᵢ))
                                                 ((A ↪) θ' sᵢ ((σ ↪s) uᵢ'))} us₀ us₀'
        iHus θ' ∼⟨⟩ = ∼⟨⟩
        iHus θ' (∼▹ {s₀} {ar₀} {u₁} {u₂} ⊢u₁≈u₂ p) = ∼▹ (correctness ⊢u₁≈u₂ A sall θ' ∼⟨⟩)
                                                       (iHus θ' p)
        θσ↪≈θ↪∘σ↪ : ∀ {s'} → (t₀ : ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) →
                        (A ⟦ s' ⟧ₛ ≈ (A ↪) θσ s' t₀) ((A ↪) θ s' ((σ ↪s) t₀))
        θσ↪≈θ↪∘σ↪ = ∘subst {A = A} σ θ
        A⊨econd : ((A ⟦ s ⟧ₛ) ≈ (A ↪) θ s ((σ ↪s) t))
                               ((A ↪) θ s ((σ ↪s) t'))
        A⊨econd = begin
                   (A ↪) θ s ((σ ↪s) t)
                     ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (θσ↪≈θ↪∘σ↪ t)⟩
                   (A ↪) θσ s t
                     ≈⟨ satAll sall econd θσ (map∼v (λ {s₀} {uᵢ} {uᵢ'} x →
                                             Setoid.trans (A ⟦ s₀ ⟧ₛ) (θσ↪≈θ↪∘σ↪ uᵢ)
                                             (Setoid.trans (A ⟦ s₀ ⟧ₛ) x (Setoid.sym (A ⟦ s₀ ⟧ₛ) (θσ↪≈θ↪∘σ↪ uᵢ'))))
                                             (iHus θ ⊢us≈us')) ⟩
                   (A ↪) θσ s t'
                     ≈⟨ θσ↪≈θ↪∘σ↪ t' ⟩
                   (A ↪) θ s ((σ ↪s) t')
                   ∎
          where open EqR (A ⟦ s ⟧ₛ)
correctness {s = s} {E} (preemp {[]} ∼⟨⟩ f) = λ { A x θ ∼⟨⟩ → Setoid.refl (A ⟦ s ⟧ₛ) }
correctness {ℓ₁} {ℓ₂} {Σ} {X} {ar} {s} {E}
            (preemp {x ∷ ar'} {.s} {ts} {ts'} ⊢ts≈ts' f) A sall θ ∼⟨⟩ =
                begin
                   (A ↪) θ s (term f ts)
                 ≈⟨ TΣXcond f ts ⟩
                   A ⟦ f ⟧ₒ ⟨$⟩ map⟿ (T Σ 〔 X 〕) A TΣX⇝A ts
                 ≈⟨ Π.cong (A ⟦ f ⟧ₒ) (map≈ (iHts ⊢ts≈ts')) ⟩
                   A ⟦ f ⟧ₒ ⟨$⟩ map⟿ (T Σ 〔 X 〕) A TΣX⇝A ts'
                 ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (TΣXcond f ts') ⟩
                   (A ↪) θ s (term f ts')
                ∎
                
  where open EqR (A ⟦ s ⟧ₛ)
        open Freeness A θ
        iHts : ∀ {ar₀} {ts₀ ts₀' : HVec (λ s' → ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) ar₀} →
               _∼v_ {R = λ sᵢ tᵢ tᵢ' → E ⊢ (⋀ tᵢ ≈ tᵢ')} ts₀ ts₀' →
               _∼v_ {R = λ sᵢ tᵢ tᵢ' → (A ⟦ sᵢ ⟧ₛ ≈ (A ↪) θ sᵢ tᵢ)
                                                 ((A ↪) θ sᵢ tᵢ')} ts₀ ts₀'
        iHts {[]} {⟨⟩} ∼⟨⟩ = ∼⟨⟩
        iHts {s₀ ∷ ar₀} {t₀ ▹ ts₀} {t₀' ▹ ts₀'} (∼▹ ⊢t₀≈t₀' ⊢ts₀≈ts₀') =
                                    ∼▹ (ih ⊢t₀≈t₀' A sall θ ∼⟨⟩) (iHts ⊢ts₀≈ts₀')
          where ih : ∀ {s' : sorts Σ} {tᵢ tᵢ' : ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥} →
                       E ⊢ (⋀ tᵢ ≈ tᵢ') → ⊨All E (⋀ tᵢ ≈ tᵢ')
                ih {s'} {tᵢ} {tᵢ'} peq = correctness peq
        map≈ : ∀ {ar'} {ts₀ ts₀' : HVec (λ s' → ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) ar'} →
               (p : _∼v_ {R = λ sᵢ tᵢ tᵢ' → (A ⟦ sᵢ ⟧ₛ ≈ (A ↪) θ sᵢ tᵢ)
                                                 ((A ↪) θ sᵢ tᵢ')} ts₀ ts₀') →
               _∼v_ {R = λ s₀ → _≈_ (A ⟦ s₀ ⟧ₛ)}
               (map⟿ (T Σ 〔 X 〕) A TΣX⇝A ts₀) (map⟿ (T Σ 〔 X 〕) A TΣX⇝A ts₀')
        map≈ {[]} ∼⟨⟩ = ∼⟨⟩
        map≈ {i ∷ is} {t₀ ▹ ts₀} {t₀' ▹ ts₀'} (∼▹ p₀ p) = ∼▹ p₀ (map≈ p)


-- Completeness

⊢R : ∀ {Σ X ar} → (E : Theory Σ X ar) → (s : sorts Σ) →
       Rel (∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥) _
⊢R E s = λ t t' → E ⊢ (⋀ t ≈ t') 

⊢REquiv : ∀ {Σ X ar} → (E : Theory Σ X ar) → (s : sorts Σ) →
          IsEquivalence (⊢R E s)
⊢REquiv E s = record { refl = prefl
                     ; sym = psym
                     ; trans = ptrans
                     }

⊢RSetoid : ∀ {Σ X ar} → (E : Theory Σ X ar) → (s : sorts Σ) → Setoid _ _
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
        
⊢Quot : ∀ {Σ X ar} → (E : Theory Σ X ar) → Algebra Σ
⊢Quot {Σ} {X} E = Quotient T Σ 〔 X 〕 (⊢Cong E)

⊢Quot⊨E : ∀ {Σ X ar} → (E : Theory Σ X ar) → ⊨T E (⊢Quot E)
⊢Quot⊨E {Σ} {X} {ar} E = record { satAll = sall }
  where sall : ∀ {s} {e : Equation Σ X s} → e ∈ E → (⊢Quot E) ⊨ e
        sall {s} {⋀ t ≈ t' if「 ar 」 (us , us')} e∈E θ ⊢θuᵢ≈θuᵢ' = {!psubst e∈E θ ?!} --psubst {!e∈E!} θ {!⊢θuᵢ≈θuᵢ'!}

complete : ∀ {ℓ₁ ℓ₂ Σ X} {ar : Arity Σ} {s : sorts Σ} {E : Theory Σ X ar}
             {t t' : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥ } →
             ⊨All {ℓ₁} {ℓ₂} E (⋀ t ≈ t') → E ⊢ (⋀ t ≈ t')
complete {ℓ₁} {ℓ₂} {Σ} {X} {ar} {s} {E} {t} {t'} sall = {!⊢Quot⊨e (idSubst X) ?!}
  where ⊢Quot⊨e : ⊢Quot E ⊨ (⋀ t ≈ t')
        ⊢Quot⊨e = {!!} --sall (⊢Quot Σ X E) (⊢Quot⊨E E)
         

