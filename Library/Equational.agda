-- Universal Algebra Library
--
-- Conditional equational logic:
-- equations, equational theories, proofs, models, soundness and
-- completeness. Implication of theories.
--
open import UnivAlgebra
module Equational (Σ : Signature) where

open import Data.List hiding (zip;zipWith)
open import Data.Product hiding (Σ;zip)
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

-- An unconditional equation is just a pair of terms.
record Equ (X : Vars Σ) (s : sorts Σ) : Set where
  constructor _≈ₑ_
  field
    eleft  : TΣ〔 X 〕 ∥ s ∥
    eright : TΣ〔 X 〕 ∥ s ∥

{- Equations -}
record Equation (s : sorts Σ) : Set₁ where
  constructor ⋀_,_if_
  field
    X : Vars Σ
    eq  : Equ X s
    cond : Σ[ ar ∈ Arity Σ ] (HVec (Equ X) ar)

  open Equ

  left = eleft eq
  right = eright eq

{- Unconditional equation -}
⋀_,_≈_ : ∀ X {s} → (t t' : TΣ〔 X 〕 ∥ s ∥) → Equation s
⋀ X , t ≈ t' = ⋀ X , (t ≈ₑ t') if ([] , ⟨⟩)

infix 0 ⋀_,_≈_

Theory : (ar : Arity Σ) → Set₁
Theory ar = HVec Equation ar

equ-to-Equation : ∀ X s → Equ X s → Equation s
equ-to-Equation X s equ = ⋀ X ,  (eleft equ) ≈ (eright equ)
  where open Equ

EqTheory : (X : Vars Σ) → (ar : Arity Σ) → Set
EqTheory X ar = HVec (Equ X) ar

eqTheory-to-Theory : ∀ {X ar} → EqTheory X ar → Theory ar
eqTheory-to-Theory {X} = mapV (equ-to-Equation X)

open Equation
equation-to-Equ : ∀ s → (e : Equation s) → Equ (X e) s
equation-to-Equ _ equ = record { eleft = left equ ; eright = right equ }


iso-equ : ∀ {X} s → (eq : Equ X s) →
        eq ≡ equation-to-Equ s (equ-to-Equation X s eq)
iso-equ s record { eleft = t ; eright = t' } = PE.refl
  where open Equ


{- Satisfactibility -}
_,_⊨ₑ_ : ∀  {X : Vars Σ} {ℓ₁ ℓ₂} (A : Algebra {ℓ₁} {ℓ₂} Σ) →
       (θ : Env X A ) → {s : sorts Σ} → Equ X s → Set ℓ₂
_,_⊨ₑ_ {X} A θ {s} (t ≈ₑ t') = eval θ t ≈ eval θ t'
  where
  open Eval X A
  open Setoid (A ⟦ s ⟧ₛ)
_⊨c_ : ∀ {X : Vars Σ}  {ℓ₁ ℓ₂} (A : Algebra {ℓ₁} {ℓ₂} Σ) {s : sorts Σ} →
       Equ X s → Set (ℓ₁ ⊔ ℓ₂)
_⊨c_ {X = X} A {s} equ = (θ : Env X A ) → A , θ ⊨ₑ equ


_⊨_ : ∀ {ℓ₁ ℓ₂} (A : Algebra {ℓ₁} {ℓ₂} Σ) {s : sorts Σ} →
      Equation s → Set (ℓ₁ ⊔ ℓ₂)
_⊨_ A {s} (⋀ X , equ if (ar , conds)) =
    (θ : Env X A ) → (A , θ ⊨ₑ_) ⇨v conds → A , θ ⊨ₑ equ


{- A is model -}
_⊨T_ : ∀ {ar ℓ₁ ℓ₂} → (A : Algebra {ℓ₁} {ℓ₂} Σ) →
       (E : Theory ar) → Set _
A ⊨T E = ∀ {s e} → _∈_ {i = s} e E → A ⊨ e



⊨All : ∀ {ℓ₁ ℓ₂} {ar : Arity Σ} {s : sorts Σ} → (E : Theory ar) →
       (e : Equation s) → Set (lsuc ℓ₂ Level.⊔ lsuc ℓ₁)
⊨All {ℓ₁} {ℓ₂} E e = (A : Algebra {ℓ₁} {ℓ₂} Σ) → A ⊨T E → A ⊨ e

open Equ

module _ where
  {- Provability -}
  open Subst
  data _⊢_  {ar : Arity Σ} (E : Theory ar) : ∀ {s} → Equation s → Set₁ where
    prefl : ∀ {X s} {t : TΣ〔 X 〕 ∥ s ∥} → E ⊢ (⋀ X , t ≈ t)

    psym : ∀ {X s} {t t' : TΣ〔 X 〕 ∥ s ∥} → E ⊢ (⋀ X , t ≈ t') →
                                                    E ⊢ (⋀ X , t' ≈ t)
    ptrans : ∀ {X s} {t₀ t₁ t₂ : TΣ〔 X 〕 ∥ s ∥} →
                   E ⊢ (⋀ X , t₀ ≈ t₁) → E ⊢ (⋀ X , t₁ ≈ t₂) → E ⊢ (⋀ X , t₀ ≈ t₂)
    psubst : ∀ {Y X s} {ar'} {eqs : HVec (Equ Y) ar'}
             {t t' : TΣ〔 Y 〕 ∥ s ∥} →
             (⋀ Y , (t ≈ₑ t') if (ar' , eqs)) ∈ E →
             (σ : Subst {Σ} {Y} {X}) →
             (λ x → E ⊢ (⋀ X , (eleft x /s σ) ≈ (eright x /s σ))) ⇨v eqs →
             E ⊢ (⋀ X , t /s σ ≈ t' /s σ )

    preemp : ∀ {X} {ar'} {s} {ts ts' : HVec (λ s' → TΣ〔 X 〕 ∥ s' ∥) ar'} →
               (E ⊢_) ⇨v (zipWith (⋀_,_≈_ X) ts ts') →
               {f : ops (_〔_〕 X) (ar' , s)} →
               E ⊢ (⋀ X , term f ts ≈ term f ts')

  _∼⊢-to-⇨ : ∀ {X} {ar' : Arity Σ} (E : Theory ar') {ar}
             {ts ts' : HVec (_∥_∥ TΣ〔 X 〕) ar} →
             _∼v_ {R = λ t t' → E ⊢ (⋀ X , t ≈ t')} ts ts' →
             (E ⊢_) ⇨v (zipWith (⋀_,_≈_ X) ts ts')
  (E ∼⊢-to-⇨) {[]} ∼⟨⟩ = ⇨v⟨⟩
  (E ∼⊢-to-⇨) {_ ∷ _} (∼▹ eq eqs) = ⇨v▹ eq ((E ∼⊢-to-⇨) eqs)


  -- Syntactic sugar
  _∣_ : ∀ {X Y} {ar : Arity Σ} {E : Theory ar} {s}
             {t t' : TΣ〔 X 〕 ∥ s ∥} →
             (⋀ X , t ≈ t') ∈ E → (σ : Subst {Σ} {X} {Y}) →
             E ⊢ (⋀ Y , t /s σ ≈ t' /s σ)
  ax ∣ σ = psubst ax σ ⇨v⟨⟩


module Provable-Equivalence {X} {ar : Arity Σ} (E : Theory ar) where

  -- Equivalence relation on TΣ(X) induced by the rules.
  ⊢-≈ : (s : sorts Σ) → Rel (TΣ〔 X 〕 ∥ s ∥) (lsuc 0ℓ)
  ⊢-≈ s t t' = E ⊢ (⋀ X , t ≈ t')

  ⊢-≈Equiv : (s : sorts Σ) → IsEquivalence (⊢-≈ s)
  ⊢-≈Equiv s = record
    { refl = prefl
    ; sym = psym
    ; trans = ptrans
    }

  ⊢-≈Setoid : (s : sorts Σ) → Setoid 0ℓ (lsuc 0ℓ)
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
    pcsubst : ∀ {ar} {s : sorts Σ} (f : ops Σ (ar ↦ s)) →
            (⊢-≈ _ *) =[ _⟨$⟩_ (TΣ〔 X 〕 ⟦ f ⟧ₒ) ]⇒ ⊢-≈ s
    pcsubst {[]} f {.⟨⟩} {.⟨⟩} ∼⟨⟩ = preemp ⇨v⟨⟩
    pcsubst {x ∷ ar} f {ts} {ts'} conds = preemp  ((E ∼⊢-to-⇨) conds) {f = f}


-- Soundness and completeness of the equational calculus.
module Soundness {ar : Arity Σ} {E : Theory ar} where
  open Hom
  open Setoid
  open Subst {Σ}

  soundness : ∀ {ℓ₁ ℓ₂} {s} {e : Equation s} → E ⊢ e → ⊨All {ℓ₁} {ℓ₂} E e
  soundness {s = s} prefl A _ _ _ = refl (A ⟦ s ⟧ₛ)
  soundness {s = s} (psym t₁≈t₀) A A⊨E θ ⇨v⟨⟩ =
    sym (A ⟦ s ⟧ₛ) (soundness t₁≈t₀ A A⊨E θ ⇨v⟨⟩)
  soundness {s = s} (ptrans t₀≈t₁ t₁≈t₂) A x θ ⇨v⟨⟩ =
    trans (A ⟦ s ⟧ₛ) (soundness t₀≈t₁ A x θ ⇨v⟨⟩) (soundness t₁≈t₂ A x θ ⇨v⟨⟩)
  soundness {s = s}
              (psubst {Y = Y} {X} {t = t} {t'} e∈E σ ⊢us≈us') A A⊨E θ ⇨v⟨⟩ = begin
                   ⟦ ⟦ t ⟧σ ⟧θ
                ≈⟨ subst-theo s t ⟩
                   ⟦ t ⟧θσ
                ≈⟨ A⊨E e∈E θ∘σ ( IHus ⊢us≈us' ) ⟩
                   ⟦ t' ⟧θσ
                ≈⟨ sym (A ⟦ s ⟧ₛ) (subst-theo s t') ⟩
                   ⟦ ⟦ t' ⟧σ ⟧θ
                ∎
    where
    open SubstitutionTheorem Σ Y X A θ σ
      renaming (⟦_⟧ησ to ⟦_⟧θσ;⟦_⟧η to ⟦_⟧θ; ση to θ∘σ)
    open Eval X A
    IHus : ∀ {ar₀} {eqs : HVec (Equ Y) ar₀} →
           (λ x → E ⊢ (⋀ X , (eleft x /s σ) ≈ (eright x /s σ))) ⇨v eqs →
           (λ { {sᵢ} (uᵢ ≈ₑ uᵢ') → _≈_ (A ⟦ sᵢ ⟧ₛ) ⟦ uᵢ ⟧θσ ⟦ uᵢ' ⟧θσ}) ⇨v eqs
    IHus {[]} {⟨⟩} ⇨v⟨⟩ = ⇨v⟨⟩
    IHus {s' ∷ _} {(u₁ ≈ₑ u₁') ▹ _} (⇨v▹ pv prf) = ⇨v▹ ihₒ (IHus prf)
      where
      open EqR (A ⟦ s' ⟧ₛ)
      ihₒ = begin
        ⟦ u₁ ⟧θσ       ≈⟨ sym (A ⟦ s' ⟧ₛ) (subst-theo s' u₁) ⟩
        ⟦ ⟦ u₁ ⟧σ ⟧θ   ≈⟨ soundness pv A A⊨E θ ⇨v⟨⟩ ⟩
        ⟦ ⟦ u₁' ⟧σ ⟧θ  ≈⟨ subst-theo s' u₁' ⟩
        ⟦ u₁' ⟧θσ      ∎
    open EqR (A ⟦ s ⟧ₛ)

  soundness {s = s} (preemp {ar' = []} {ts = ⟨⟩} {⟨⟩} ⇨v⟨⟩ {f}) A A⊨E θ ⇨v⟨⟩ = refl (A ⟦ s ⟧ₛ)
  soundness (preemp {X} {x ∷ _} {s} {ts} {ts'} ⊢ts≈ts' {f}) A A⊨E θ ⇨v⟨⟩ = begin
    eval θ (term f ts)                         ≈⟨ TΣXcond f ts ⟩
    A ⟦ f ⟧ₒ ⟨$⟩ map⟿ (TΣ〔 X 〕) A TΣX⇝A ts  ≈⟨ Π.cong (A ⟦ f ⟧ₒ) (IHts ⊢ts≈ts') ⟩
    A ⟦ f ⟧ₒ ⟨$⟩ map⟿ (TΣ〔 X 〕) A TΣX⇝A ts' ≈⟨ sym (A ⟦ s ⟧ₛ) (TΣXcond f ts') ⟩
    eval θ (term f ts') ∎
    where
    open EqR (A ⟦ s ⟧ₛ)
    open Eval X A hiding (TΣX⇝A;TΣXcond)
    open Eval X A θ hiding (eval)
    IHts : ∀ {ar'} {ts ts' : HVec (TΣ〔 X 〕 ∥_∥) ar'} →
           ((E ⊢_) ⇨v (zipWith (⋀_,_≈_ X) ts ts')) →
           _∼v_ {R = λ {s₀} → _≈_ (A ⟦ s₀ ⟧ₛ)}
                (map⟿ (TΣ〔 X 〕) A TΣX⇝A ts) (map⟿ (TΣ〔 X 〕) A TΣX⇝A ts')
    IHts {[]} {⟨⟩} {⟨⟩} ⇨v⟨⟩ = ∼⟨⟩
    IHts {_ ∷ _} {_ ▹ _} {_ ▹ _} (⇨v▹ eq eqs) =
      ∼▹ (soundness eq A A⊨E θ ⇨v⟨⟩) (IHts eqs)

module Completeness {ar : Arity Σ} {E : Theory ar} {X : Vars Σ} where
  open Provable-Equivalence {X} E


  ⊢Quot : Algebra {0ℓ} {lsuc 0ℓ} Σ
  ⊢Quot = TΣ〔 X 〕 / ⊢Cong
  open Subst

  module ⊢QuotSubst (Y : Vars Σ) (θ : Subst {Σ} {Y} {X}) where
    open Eval Y ⊢Quot renaming (eval* to subst*)
    open Eval Y (TΣ〔 X 〕) hiding (eval)

    thm : ∀ {s} → (t : TΣ〔 Y 〕 ∥ s ∥) → (eval θ t) ≡ (t /s θ)
    thm' : ∀ {ar'} (ts : HVec (TΣ〔 Y 〕 ∥_∥) ar') → subst* θ ts ≡ eval* θ ts
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

    A⊨E : ∀ {s} {e : Equation s} → _∈_ {is = ar} e E → ⊢Quot ⊨ e
    A⊨E {s} {e = (⋀ Y , (t ≈ₑ t') if (_ , _))} e∈E θ us~us' =
      welldef ⊢Cong s (S.sym (thm t) , S.sym (thm t')) tσ≈t'σ
      where
      open Congruence
      open EqR (⊢-≈Setoid s)
      module S = Setoid (TΣ〔 X 〕 ⟦ s ⟧ₛ)
      open ⊢QuotSubst Y θ
      tσ≈t'σ : E ⊢ (⋀ X , (t /s θ) ≈ (t' /s θ))
      tσ≈t'σ = psubst e∈E θ
       (map⇨v (λ { {s'} {t₁ ≈ₑ t₂} eq → welldef ⊢Cong s' (thm t₁ , thm t₂) eq }) us~us')

  completeness : ∀ {s} {t t' : TΣ〔 X 〕 ∥ s ∥ } →
                 ⊨All {0ℓ} {lsuc 0ℓ} E (⋀ X , t ≈ t') →
                 E ⊢ (⋀ X , t ≈ t')
  completeness {s} {t} {t'} A⊨E = begin
    t              ≈⟨ ≡to≈ (⊢-≈Setoid s) (PE.sym (subst-id t)) ⟩
    t /s idSubst   ≈⟨ welldef ⊢Cong s (thm t , thm t') (A⊨E ⊢Quot ⊢Quot⊨E idSubst ⇨v⟨⟩) ⟩
    t' /s idSubst  ≈⟨ ≡to≈ (⊢-≈Setoid s) (subst-id t') ⟩
    t' ∎
    where
    open IdSubst Σ X
    open Congruence
    open EqR (⊢-≈Setoid s)
    open Eval X (⊢Quot)
    open Eval X (TΣ〔 X 〕) hiding (eval) renaming (eval* to map↪ₜ)
    open ⊢QuotSubst X idSubst

-- A theory E implies a theory E' if every axiom of E' is provable in E.
module Theory-Implication where

  _⇒T_ : ∀ {ar ar'} → Theory ar → Theory ar' → Set₁
  _⇒T_ E E' = ∀ {s} {ax : Equation s} → ax ∈ E' → E ⊢ ax

  ⊨T⇒ : ∀ {ℓ₁ ℓ₂ ar ar'} → (E : Theory ar) (E' : Theory ar')
        (E⇒E' : E ⇒T E') → (A : Algebra {ℓ₁} {ℓ₂} Σ) → A ⊨T E → A ⊨T E'
  ⊨T⇒ E E' E⇒E' A A⊨E ax θ A⊨conds = soundness (E⇒E' ax) A A⊨E θ A⊨conds
    where open Soundness {E = E}

{- Initiality of the Quotiened Term Algebra; ie, the term model -}
module InitialityModel {X ar ℓ₁ ℓ₂} {E : Theory ar}
                         {A : Algebra {ℓ₁} {ℓ₂} Σ} (M : A ⊨T E) (θ : Env X A)
         where
    open Soundness {E = E}
    open Completeness {E = E} {X = X}
    open Hom ⊢Quot A
    open Homo

    init : Homo
    init = record
      { ′_′ = λ s → record
          { _⟨$⟩_ = _⟨$⟩_ ( ′ TΣXHom ′ s)
          ; cong = λ {j} {i} E⊢e → soundness E⊢e A M θ ⇨v⟨⟩
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

    UMP-⊢ : (H H' : Homo) → extends (liftH H) → extends (liftH H') →
      H ≈ₕ H'
    UMP-⊢ H H' ext ext' = UMP (liftH H) (liftH H') ext ext'
