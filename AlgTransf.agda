module AlgTransf where

open import UnivAlgebra

open import Relation.Binary
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Nat renaming (_⊔_ to _⊔ₙ_)
open import Data.Product renaming (map to pmap)
open import Function
open import Function.Equality renaming (_∘_ to _∘ₛ_)
open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality as PE
open import Induction.WellFounded
open import Data.String
open import Data.Fin hiding (#_)
open import VecH

{- Transformación entre álgebras.
   Si tenemos una manera de llevar los sorts de una signatura Σ₀
   en sorts de una signatura Σ₁ y de escribir cada símbolo de función
   de Σ₀ como composición de símbolos de Σ₁, entonces a partir
   de un álgebra de Σ₁ podemos obtener un álgebra de Σ₀. -}

open Signature

{-
Para llevar elementos de una Σ'-álgebra en una Σ-álgebra
definimos un lenguaje para traducir los símbolos de función
de Σ a 'expresiones' de Σ'. Estas expresiones están definidas
en SigExpr:
-}

{-
la aridad ar contiene información del contexto donde ocurre
la expresión. Los sorts de ar serán los correspondientes a
variables
-}
data ΣExpr (Σ : Signature) (ar : Arity Σ) : (sorts Σ) → Set where
  #      : (n : Fin (length ar)) → ΣExpr Σ ar (ar ‼ n)
  _∣$∣_   : ∀ {ar'} {s} → (f : funcs Σ (ar' , s)) →
             (es : VecH (sorts Σ) (ΣExpr Σ ar) ar') → ΣExpr Σ ar s


-- Transformación de una signatura Σ₀ en una Σ₁
record _↝_ (Σ₀ : Signature) (Σ₁ : Signature) : Set where
  field
    ↝ₛ  : sorts Σ₀ → sorts Σ₁
    ↝f : ∀ {ar} {s} → (f : funcs Σ₀ (ar , s)) →
                        ΣExpr Σ₁ (map ↝ₛ ar) (↝ₛ s) 

-- Mapeo de sorts de una signatura a otra
mapsorts : ∀ {Σ₀} {Σ₁} → (sorts Σ₀ → sorts Σ₁) →
             ΣType Σ₀ → ΣType Σ₁
mapsorts fₛ = pmap (map fₛ) fₛ


open _↝_
open Algebra
open Setoid


mutual
  iΣExpr : ∀ {l₀} {l₁} {Σ : Signature} {ar : Arity Σ} {s : sorts Σ}→
                    (a : Algebra {l₀} {l₁} Σ) →
                    (vs : VecH (sorts Σ) (Carrier ∘ _⟦_⟧ₛ a) ar) →
                    (e : ΣExpr Σ ar s) → Carrier (a ⟦ s ⟧ₛ)
  iΣExpr a vs (# n) = vs ‼v n
  iΣExpr a vs (f ∣$∣ es) = a ⟦ f ⟧ ⟨$⟩ mapvec a vs es

  -- mapvec es igual a mapV interpSigExpr, pero hay que definirlo
  -- así porque sino el chequeador de terminación de Agda se queja. 
  mapvec :  ∀ {l₀} {l₁} {Σ : Signature} {ar ar' : Arity Σ} →
              (a : Algebra {l₀} {l₁} Σ) →
              (vs : VecH (sorts Σ) (Carrier ∘ _⟦_⟧ₛ a) ar) →
              (es : VecH (sorts Σ) (ΣExpr Σ ar) ar') →
              VecH (sorts Σ) (Carrier ∘ _⟦_⟧ₛ a) ar'
  mapvec a _ ⟨⟩ = ⟨⟩
  mapvec a vs (e ▹ es) = (iΣExpr a vs e) ▹ mapvec a vs es 


{- Transformación de la interpretación de un símbolo de función -}
interpFunTrans : ∀ {l₀ l₁} {Σ₀ Σ₁ : Signature} {ar : Arity Σ₀}
                   {s : sorts Σ₀} {fₛ : sorts Σ₀ → sorts Σ₁} →
                   (f : funcs Σ₀ (ar , s)) → (e : ΣExpr Σ₁ (map fₛ ar) (fₛ s)) →
                   (a : Algebra {l₀} {l₁} Σ₁) → 
                   IFuncs Σ₀ (ar , s) (_⟦_⟧ₛ a ∘ fₛ)
interpFunTrans {Σ₀ = Σ₀} {Σ₁} {ar} {s} {fₛ} f e a =
                   record { _⟨$⟩_ = λ vs → iΣExpr a
                                           (vecTransf fₛ (Carrier ∘ _⟦_⟧ₛ a) ar vs) e
                          ; cong = λ vs≈vs' → fTransCong e (∼vtransf fₛ vs≈vs') }
  where fTransCong : ∀ {ar₁ : Arity Σ₁} {s₁ : sorts Σ₁}
                       {vs vs' : VecH (sorts Σ₁) (Carrier ∘ _⟦_⟧ₛ a) ar₁} →
                       (e₁ : ΣExpr Σ₁ ar₁ s₁) →
                       _∼v_ {R = _≈_ ∘ _⟦_⟧ₛ a} vs vs' → _≈_ (a ⟦ s₁ ⟧ₛ)
                       (iΣExpr a vs e₁) (iΣExpr a vs' e₁)
        fTransCong {vs = vs} {vs'} (# n) eq = ~v‼prop vs vs' eq n
        fTransCong {ar₁ = ar₁} {_} {vs} {vs'} (_∣$∣_ {arₑ} f₁ es) eq =
                                              Π.cong (a ⟦ f₁ ⟧) (≈mapvec arₑ es)
          where ≈mapvec : (ar' : Arity Σ₁) →
                          (ws : VecH (sorts Σ₁) (ΣExpr Σ₁ ar₁) ar') →
                          (mapvec a vs ws) ∼v (mapvec a vs' ws)
                ≈mapvec .[] ⟨⟩ = ∼⟨⟩
                ≈mapvec {s' ∷ ar'} (v ▹ ws) = ∼▹ (fTransCong v eq)
                                                 (≈mapvec ar' ws)


funAlgTransf : ∀ {l₀ l₁} {Σ₀ Σ₁} {ty : ΣType Σ₀} (t : Σ₀ ↝ Σ₁) →
                 (a : Algebra {l₀} {l₁} Σ₁) →
                 (f : funcs Σ₀ ty) →
                 IFuncs Σ₀ ty (_⟦_⟧ₛ a ∘ (↝ₛ t))
funAlgTransf {Σ₀ = Σ₀} {Σ₁ = Σ₁} t a f = interpFunTrans {Σ₀ = Σ₀} f (↝f t f) a


-- Transformación de un álgebra de Σ₁ en una de Σ₀
_〈_〉 : ∀ {l₀} {l₁} {Σ₀} {Σ₁} → (t : Σ₀ ↝ Σ₁) →
            (a : Algebra {l₀} {l₁} Σ₁) → Algebra {l₀} {l₁} Σ₀
t 〈 a 〉 = (_⟦_⟧ₛ a ∘ ↝ₛ t) ∥ funAlgTransf t a



open Homomorphism

-- La condición de homomorfismo se preserva en una transformación.
homCond↝ : ∀ {l₀ l₁} {Σ₀ Σ₁ : Signature} {a a' : Algebra {l₀} {l₁} Σ₁}
             {ty : ΣType Σ₀} → (t : Σ₀ ↝ Σ₁) → (h : Homomorphism a a') → 
             (f : funcs Σ₀ ty) → homCond (t 〈 a 〉) (t 〈 a' 〉) (′ h ′ ∘ ↝ₛ t) f
homCond↝ {Σ₁ = Σ₁} {a} {a'} {ar , s} t h f = λ as →
               subst (λ vec → _≈_ (a' ⟦ ↝ₛ t s ⟧ₛ)
                                   (_⟨$⟩_ (′ h ′ (↝ₛ t s))
                                         (iΣExpr a (vecTransf (↝ₛ t) (Carrier ∘ _⟦_⟧ₛ a) ar as)
                                          (↝f t f)))
                                   (iΣExpr a' vec (↝f t f)))
                     (≡maptransf (↝ₛ t) (Carrier ∘ _⟦_⟧ₛ a) (Carrier ∘ _⟦_⟧ₛ a')
                                 (_⟨$⟩_ ∘ ′ h ′) ar as)
                     (homCond↝' (map (↝ₛ t) ar) (↝ₛ t s) (↝f t f)
                                 (vecTransf (↝ₛ t) (Carrier ∘ _⟦_⟧ₛ a) ar as))
  where
        homCond↝' : (ar : Arity Σ₁) → (s : sorts Σ₁) → (e : ΣExpr Σ₁ ar s) →
                     (vs : VecH (sorts Σ₁) (Carrier ∘ _⟦_⟧ₛ a) ar) →
                     _≈_ (a' ⟦ s ⟧ₛ )
                     (′ h ′ s ⟨$⟩ iΣExpr a vs e)
                     (iΣExpr a' (map⟿ {Σ = Σ₁} {a} {a'} ′ h ′ vs) e)
        homCond↝' [] _ (# ()) ⟨⟩
        homCond↝' (s ∷ ar) .s (# zero) (v ▹ vs) = Setoid.refl (a' ⟦ s ⟧ₛ)
        homCond↝' (s ∷ ar) .(ar ‼ n) (# (suc n)) (v ▹ vs) = homCond↝' ar (ar ‼ n) (# n) vs
        homCond↝' ar s (_∣$∣_ {ar₁} f₁ es) vs =
                   Setoid.trans (a' ⟦ s ⟧ₛ) (cond h f₁ (mapvec a vs es))
                                            (Π.cong (a' ⟦ f₁ ⟧)
                                                    (homCond↝'vec ar₁ es))
          where homCond↝'vec : (ar₁ : Arity Σ₁) → 
                               (es : VecH (sorts Σ₁) (ΣExpr Σ₁ ar) ar₁) →
                               _∼v_ {R = _≈_ ∘ _⟦_⟧ₛ a'}
                               (mapV (λ x → _⟨$⟩_ (′ h ′ x)) (mapvec a vs es))
                               (mapvec a' (mapV (λ x → _⟨$⟩_ (′ h ′ x)) vs) es)
                homCond↝'vec .[] ⟨⟩ = ∼⟨⟩
                homCond↝'vec (s₁ ∷ ar₁) (e ▹ es) = ∼▹ (homCond↝' ar s₁ e vs)
                                                       (homCond↝'vec ar₁ es)




{- Si tenemos un homomorfismo entre álgebras de Σ₁ y tenemos
   una transformación de Σ₀ en Σ₁, entonces podemos obtener
   un homomorfismo entre las álgebras transformadas de Σ₀ -}
_〈_〉ₕ : ∀ {l₀ l₁} {Σ₀ Σ₁ : Signature} {a a' : Algebra {l₀} {l₁} Σ₁} →
              (t : Σ₀ ↝ Σ₁) → (h : Homomorphism a a') →
              Homomorphism (t 〈 a 〉) (t 〈 a' 〉)
t 〈 h 〉ₕ = record { ′_′ = ′ h ′ ∘ ↝ₛ t
                  ; cond = homCond↝ t h
                  }

