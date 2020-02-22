-- Universal Algebra Library
--
-- Conditional equational logic:
-- equations, equational theories, proofs, models, soundness and
-- completeness. Implication of theories.
--
open import UnivAlgebra
module Equational (Σ : Signature) where

open import Data.List
open import Data.Product hiding (Σ)
open import Data.Sum hiding (map)
open import Function as F
open import Function.Equality as FE renaming (_∘_ to _∘e_)
open import Level renaming (zero to lzero ; suc to lsuc)
open import Relation.Binary hiding (Total)
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.PropositionalEquality using (_≡_;cong₂)
import Relation.Binary.PropositionalEquality as PE

open import HeterogeneousVec renaming (map to mapV)
open import Morphisms
open import TermAlgebra
open import Setoids hiding (∥_∥)

open OpenTerm Σ renaming (T_〔_〕 to TΣ〔_〕)

{- Equations -}
record Equation (X : Vars Σ) (s : sorts Σ) : Set where
  constructor ⋀_≈_if「_」_
  field
    left  : TΣ〔 X 〕 ∥ s ∥
    right : TΣ〔 X 〕 ∥ s ∥
    carty : Arity Σ
    cond : HVec (λ s' → TΣ〔 X 〕 ∥ s' ∥) carty ×
           HVec (λ s' → TΣ〔 X 〕 ∥ s' ∥) carty


{- Unconditional equation -}
⋀_≈_ : ∀ {X s} → (t t' : TΣ〔 X 〕 ∥ s ∥) → Equation X s
⋀ t ≈ t' = ⋀ t ≈ t' if「 [] 」 (⟨⟩ , ⟨⟩)

infix 0 ⋀_≈_
record Equ (X : Vars Σ) (s : sorts Σ) : Set where
  field
    left  : TΣ〔 X 〕 ∥ s ∥
    right : TΣ〔 X 〕 ∥ s ∥

Theory : (X : Vars Σ) → (ar : Arity Σ) → Set
Theory X ar = HVec (Equation X) ar

equ-to-Equation : ∀ {X} s → Equ X s → Equation X s
equ-to-Equation _ equ = ⋀ (left equ) ≈ (right equ)
  where open Equ

EqTheory : (X : Vars Σ) → (ar : Arity Σ) → Set
EqTheory X ar = HVec (Equ X) ar

eqTheory-to-Theory : ∀ {X ar} → EqTheory X ar → Theory X ar
eqTheory-to-Theory = mapV equ-to-Equation

equation-to-Equ : ∀ {X} s → Equation X s → Equ X s
equation-to-Equ _ equ = record { left = left equ ; right = right equ }
  where open Equation

iso-equ : ∀ {X} s → (eq : Equ X s) →
        eq ≡ equation-to-Equ s (equ-to-Equation s eq)
iso-equ s record { left = t ; right = t' } = PE.refl
  where open Equ

{- Satisfactibility -}
_⊨_ : ∀  {X : Vars Σ} {s : sorts Σ} {ℓ₁ ℓ₂} →
        (A : Algebra {ℓ₁} {ℓ₂} Σ) → Equation X s → Set (ℓ₂ Level.⊔ ℓ₁)
_⊨_ {X = X} {s} A (⋀ t ≈ t' if「 _ 」 (us , us')) =
    (θ : Env X A ) →
    _∼v_ {R = λ {sᵢ} uᵢ uᵢ' → _≈_ (A ⟦ sᵢ ⟧ₛ) (eval θ uᵢ) (eval θ uᵢ')} us us' →
    (_≈_ (A ⟦ s ⟧ₛ)) (eval θ t) (eval θ t')
  where
  open Eval X A
  open Setoid


{- A is model -}
_⊨T_ : ∀ {X ar ℓ₁ ℓ₂} → (A : Algebra {ℓ₁} {ℓ₂} Σ) →
       (E : Theory X ar) → Set _
A ⊨T E = ∀ {s e} → _∈_ {i = s} e E → A ⊨ e

⊨All : ∀ {ℓ₁ ℓ₂ X} {ar : Arity Σ} {s : sorts Σ} → (E : Theory X ar) →
               (e : Equation X s) → Set (lsuc ℓ₂ Level.⊔ lsuc ℓ₁)
⊨All {ℓ₁} {ℓ₂} E e = (A : Algebra {ℓ₁} {ℓ₂} Σ) → A ⊨T E → A ⊨ e

module _ {X} where
  open Subst X

  {- Provability -}
  data _⊢_  {ar : Arity Σ} (E : Theory X ar) : ∀ {s} → Equation X s → Set where
    prefl : ∀ {s} {t : TΣ〔 X 〕 ∥ s ∥} → E ⊢ (⋀ t ≈ t)
    psym : ∀ {s} {t t' : TΣ〔 X 〕 ∥ s ∥} → E ⊢ (⋀ t ≈ t') →
                                                    E ⊢ (⋀ t' ≈ t)
    ptrans : ∀ {s} {t₀ t₁ t₂ : TΣ〔 X 〕 ∥ s ∥} →
                   E ⊢ (⋀ t₀ ≈ t₁) → E ⊢ (⋀ t₁ ≈ t₂) → E ⊢ (⋀ t₀ ≈ t₂)
    psubst : ∀ {s} {ar'} {us us' : HVec (λ s' → TΣ〔 X 〕 ∥ s' ∥) ar'}
             {t t' : TΣ〔 X 〕 ∥ s ∥} →
             (⋀ t ≈ t' if「 ar' 」 (us , us')) ∈ E →
             (σ : Subst) →
             _∼v_ {R = λ uᵢ uᵢ' → E ⊢ (⋀ uᵢ /s σ ≈ uᵢ' /s σ)} us us' →
             E ⊢ (⋀ t /s σ ≈ t' /s σ )
    preemp : ∀ {ar'} {s} {ts ts' : HVec (λ s' → TΣ〔 X 〕 ∥ s' ∥) ar'} →
               _∼v_ {R = λ tᵢ tᵢ' → E ⊢ (⋀ tᵢ ≈ tᵢ')} ts ts' →
               {f : ops (_〔_〕 X) (ar' , s)} → E ⊢ (⋀ term f ts ≈ term f ts')


  -- Syntactic sugar
  _∣_ : ∀ {ar : Arity Σ} {E : Theory X ar} {s}
             {t t' : TΣ〔 X 〕 ∥ s ∥} →
             (⋀ t ≈ t') ∈ E → (σ : Subst) →
             E ⊢ (⋀ t /s σ ≈ t' /s σ)
  ax ∣ σ = psubst ax σ ∼⟨⟩

module Provable-Equivalence {X} {ar : Arity Σ} (E : Theory X ar) where

  -- Equivalence relation on TΣ(X) induced by the rules.
  ⊢-≈ : (s : sorts Σ) → Rel (TΣ〔 X 〕 ∥ s ∥) (Level.zero)
  ⊢-≈ s t t' = E ⊢ (⋀ t ≈ t')

  ⊢-≈Equiv : (s : sorts Σ) → IsEquivalence (⊢-≈ s)
  ⊢-≈Equiv s = record
    { refl = prefl
    ; sym = psym
    ; trans = ptrans
    }

  ⊢-≈Setoid : (s : sorts Σ) → Setoid (Level.zero) (Level.zero)
  ⊢-≈Setoid s = record
    { Carrier = TΣ〔 X 〕 ∥ s ∥
    ; _≈_ = ⊢-≈ s
    ; isEquivalence = ⊢-≈Equiv s
    }

  ⊢Cong : Congruence (TΣ〔 X 〕)
  ⊢Cong = record
    { rel = (⊢-≈  $-)
    ; welldef = pwdef
    ; cequiv = ⊢-≈Equiv
    ; csubst = pcsubst
    }
    where
    pwdef : ∀ s → WellDefRel (TΣ〔 X 〕 ⟦ s ⟧ₛ) (⊢-≈ s)
    pwdef s {(t , t')} {(.t , .t')} (PE.refl , PE.refl) ⊢t₀≈t₁ = ⊢t₀≈t₁
    pcsubst : ∀ {ar} {s} → (f : ops Σ (ar , s)) →
                _∼v_ =[ _⟨$⟩_ (TΣ〔 X 〕 ⟦ f ⟧ₒ) ]⇒ ⊢-≈ s
    pcsubst {[]} f ∼⟨⟩ = prefl
    pcsubst {s₀ ∷ ar} {s} f {ts} {ts'} ⊢ts≈ts' = preemp ⊢ts≈ts' {f}

-- Soundness and completeness of the equational calculus.
module Soundness-Completeness {X}  {ar : Arity Σ} {E : Theory X ar} where
  open Hom
  open Setoid
  open Subst X

  soundness : ∀ {ℓ₁ ℓ₂} {s} {e : Equation X s} → E ⊢ e → ⊨All {ℓ₁} {ℓ₂} E e
  soundness {s = s} prefl A _ _ _ = refl (A ⟦ s ⟧ₛ)
  soundness {s = s} (psym t₁≈t₀) A A⊨E θ ∼⟨⟩ =
    sym (A ⟦ s ⟧ₛ) (soundness t₁≈t₀ A A⊨E θ ∼⟨⟩)
  soundness {s = s} (ptrans t₀≈t₁ t₁≈t₂) A x θ ∼⟨⟩ =
    trans (A ⟦ s ⟧ₛ) (soundness t₀≈t₁ A x θ ∼⟨⟩) (soundness t₁≈t₂ A x θ ∼⟨⟩)
  soundness {s = s}
              (psubst {t = t} {t'} e∈E σ ⊢us≈us') A A⊨E θ ∼⟨⟩ = begin
                   ⟦ ⟦ t ⟧σ ⟧θ
                ≈⟨ subst-theo s t ⟩
                   ⟦ t ⟧θσ
                ≈⟨ A⊨E e∈E θ∘σ (
                   map∼v (λ {s₀} {uᵢ} {uᵢ'} eq → A-trans (A-sym (subst-theo s₀ uᵢ))
                                               (A-trans eq (subst-theo s₀ uᵢ')) ) (IHus θ ⊢us≈us')) ⟩
                   ⟦ t' ⟧θσ
                ≈⟨ sym (A ⟦ s ⟧ₛ) (subst-theo s t') ⟩
                   ⟦ ⟦ t' ⟧σ ⟧θ
                ∎
    where
    open EqR (A ⟦ s ⟧ₛ)
    A-sym : ∀ {s} {i j} → _ → _
    A-sym {s} {i} {j} eq = sym (A ⟦ s ⟧ₛ) {i} {j} eq
    A-trans : ∀ {s} {i j k} → _ → _ → _
    A-trans {s} {i} {j} {k} eq eq' = trans (A ⟦ s ⟧ₛ) {i} {j} {k} eq eq'
    open SubstitutionTheorem X A θ σ
      renaming (⟦_⟧ησ to ⟦_⟧θσ;⟦_⟧η to ⟦_⟧θ; ση to θ∘σ)
    open Eval X A
    IHus : ∀ {ar₀} {us₀ us₀' : HVec (TΣ〔 X 〕 ∥_∥) ar₀} →
           (θ' : Env X A) →
           _∼v_ {R = λ uᵢ uᵢ' → E ⊢ (⋀ uᵢ /s σ ≈  uᵢ' /s σ )} us₀ us₀' →
           _∼v_ {R = λ {sᵢ} uᵢ uᵢ' →
                     (_≈_ (A ⟦ sᵢ ⟧ₛ) (eval θ' (uᵢ /s σ)) (eval θ' (uᵢ' /s σ)))} us₀ us₀'
    IHus θ' ∼⟨⟩ = ∼⟨⟩
    IHus θ' (∼▹ ⊢u₁≈u₂ ⊢us₁≈us₂) = ∼▹ (soundness ⊢u₁≈u₂ A A⊨E θ' ∼⟨⟩) (IHus θ' ⊢us₁≈us₂)

  soundness {s = s} (preemp {[]} ∼⟨⟩ {f}) A A⊨E θ ∼⟨⟩ = refl (A ⟦ s ⟧ₛ)
  soundness (preemp {x ∷ _} {s} {ts} {ts'} ⊢ts≈ts' {f}) A A⊨E θ ∼⟨⟩ = begin
    eval θ (term f ts)                         ≈⟨ TΣXcond f ts ⟩
    A ⟦ f ⟧ₒ ⟨$⟩ map⟿ (TΣ〔 X 〕) A TΣX⇝A ts  ≈⟨ Π.cong (A ⟦ f ⟧ₒ) (map≈ (IHts ⊢ts≈ts')) ⟩
    A ⟦ f ⟧ₒ ⟨$⟩ map⟿ (TΣ〔 X 〕) A TΣX⇝A ts' ≈⟨ sym (A ⟦ s ⟧ₛ) (TΣXcond f ts') ⟩
    eval θ (term f ts') ∎
    where
    open EqR (A ⟦ s ⟧ₛ)
    open Eval X A hiding (TΣX⇝A;TΣXcond)
    open Eval X A θ hiding (eval)
    IHts : ∀ {ar₀} {ts ts' : HVec (TΣ〔 X 〕 ∥_∥) ar₀} →
          _∼v_ {R = λ tᵢ tᵢ' → E ⊢ (⋀ tᵢ ≈ tᵢ')} ts ts' →
          _∼v_ {R = λ {sᵢ} tᵢ tᵢ' → (A ⟦ sᵢ ⟧ₛ ≈ eval θ tᵢ) (eval θ tᵢ')} ts ts'
    IHts {[]} {⟨⟩} ∼⟨⟩ = ∼⟨⟩
    IHts {s₀ ∷ ar₀} {t₀ ▹ ts₀} {t₀' ▹ ts₀'} (∼▹ ⊢t₀≈t₀' ⊢ts₀≈ts₀') =
      ∼▹ (soundness ⊢t₀≈t₀' A A⊨E θ ∼⟨⟩) (IHts ⊢ts₀≈ts₀')
    map≈ : ∀ {ar'} {ts ts' : HVec (TΣ〔 X 〕 ∥_∥) ar'} →
           (_∼v_ {R = λ {sᵢ} tᵢ tᵢ' → (A ⟦ sᵢ ⟧ₛ ≈ eval θ tᵢ) (eval θ tᵢ')} ts ts') →
           _∼v_ {R = λ {s₀} → _≈_ (A ⟦ s₀ ⟧ₛ)}
           (map⟿ (TΣ〔 X 〕) A TΣX⇝A ts) (map⟿ (TΣ〔 X 〕) A TΣX⇝A ts')
    map≈ {[]} ∼⟨⟩ = ∼⟨⟩
    map≈ {i ∷ is} {t₀ ▹ ts₀} {t₀' ▹ ts₀'} (∼▹ p₀ p) = ∼▹ p₀ (map≈ p)


  open Provable-Equivalence E
  ⊢Quot : Algebra {Level.zero} {Level.zero} Σ
  ⊢Quot = TΣ〔 X 〕 / ⊢Cong

  module ⊢QuotSubst (θ : Subst) where
    open Eval X ⊢Quot renaming (eval* to subst*)
    open Eval X (TΣ〔 X 〕) hiding (eval)

    thm : ∀ {s} → (t : TΣ〔 X 〕 ∥ s ∥) → (eval θ t) ≡ (t /s θ)
    thm' : ∀ {ar'} (ts : HVec (TΣ〔 X 〕 ∥_∥) ar') → subst* θ ts ≡ eval* θ ts
    thm (term {ar = .[]} (inj₁ k) ⟨⟩) = PE.refl
    thm (term {ar = .[]} (inj₂ x) ⟨⟩) = PE.refl
    thm (term  f (t ▹ ts)) = PE.cong (term f) (thm' (t ▹ ts))
    thm' ⟨⟩ = _≡_.refl
    thm' (t ▹ ts) = cong₂ _▹_ (thm t) (thm' ts)


  ⊢Quot⊨E : ⊢Quot ⊨T E
  ⊢Quot⊨E = A⊨E
    where
    open Eval X ⊢Quot
    open Eval X (TΣ〔 X 〕) hiding (eval) renaming (eval* to subst*)


    A⊨E : ∀ {s} {e : Equation X s} → _∈_ {is = ar} e E → ⊢Quot ⊨ e
    A⊨E {s} {e = ⋀ t ≈ t' if「 _ 」 _ } e∈E θ us~us' =
      welldef ⊢Cong s (S.sym (thm t) , S.sym (thm t')) tσ≈t'σ
      where
      open Congruence
      open EqR (⊢-≈Setoid s)
      module S = Setoid (TΣ〔 X 〕 ⟦ s ⟧ₛ)
      open ⊢QuotSubst θ
      tσ≈t'σ : E ⊢ (⋀ t /s θ ≈ t' /s θ)
      tσ≈t'σ = psubst e∈E θ
        (map∼v (λ {s'} {t₁} {t₂} → welldef ⊢Cong s' (thm t₁ , thm t₂)) us~us')

  completeness : ∀ {s} {t t' : TΣ〔 X 〕 ∥ s ∥ } →
                 ⊨All {0ℓ} {0ℓ} E (⋀ t ≈ t') →
                 E ⊢ (⋀ t ≈ t')
  completeness {s} {t} {t'} A⊨E = begin
    t              ≈⟨ ≡to≈ (⊢-≈Setoid s) (PE.sym (subst-id t)) ⟩
    t /s idSubst   ≈⟨ welldef ⊢Cong s (thm t , thm t') (A⊨E ⊢Quot ⊢Quot⊨E idSubst ∼⟨⟩) ⟩
    t' /s idSubst  ≈⟨ ≡to≈ (⊢-≈Setoid s) (subst-id t') ⟩
    t' ∎
    where
    open Congruence
    open EqR (⊢-≈Setoid s)
    open Eval X (⊢Quot)
    open Eval X (TΣ〔 X 〕) hiding (eval) renaming (eval* to map↪ₜ)
    open ⊢QuotSubst idSubst

-- A theory E implies a theory E' if every axiom of E' is provable in E.
module Theory-Implication {X} where

  _⇒T_ : ∀ {ar ar'} → Theory X ar → Theory X ar' → Set
  _⇒T_ E E' = ∀ {s} {ax : Equation X s} → ax ∈ E' → E ⊢ ax

  ⊨T⇒ : ∀ {ℓ₁ ℓ₂ ar ar'} → (E : Theory X ar) (E' : Theory X ar')
        (E⇒E' : E ⇒T E') → (A : Algebra {ℓ₁} {ℓ₂} Σ) → A ⊨T E → A ⊨T E'
  ⊨T⇒ E E' E⇒E' A A⊨E ax = soundness (E⇒E' ax) A A⊨E
    where open Soundness-Completeness {X = X} {E = E}

{- Initiality of the Quotiened Term Algebra; ie, the term model -}
module InitialityModel {X ar ℓ₁ ℓ₂} {E : Theory X ar}
                         {A : Algebra {ℓ₁} {ℓ₂} Σ} (M : A ⊨T E) (θ : Env X A)
         where
    open Soundness-Completeness {E = E}
    open Hom ⊢Quot A
    open Homo

    init : Homo
    init = record
      { ′_′ = λ s → record
          { _⟨$⟩_ = _⟨$⟩_ ( ′ TΣXHom ′ s)
          ; cong = λ {j} {i} E⊢e → soundness E⊢e A M θ ∼⟨⟩
          }
      ; cond = λ f as → TΣXcond f as
      }
      where open Eval X A θ

    open EvalUMP X A θ
    liftH : Homo → Hom.Homo (OpenTerm.T Σ 〔 X 〕) A
    liftH H = record
      { ′_′ = λ s → record { _⟨$⟩_ = λ { x →  ′ H ′ s ⟨$⟩ x }
            ; cong = λ { PE.refl → Setoid.refl (A ⟦ s ⟧ₛ) }
            }
      ; cond = λ f as → cond H f as
      }

    UMP-model : (H H' : Homo) → extends (liftH H) → extends (liftH H') →
      H ≈ₕ H'
    UMP-model H H' ext ext' = UMP (liftH H) (liftH H') ext ext'
