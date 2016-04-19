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
open import Data.Fin
open import VecH

{- Transformación entre álgebras.
   Si tenemos una manera de llevar los sorts de una signatura S₀
   en sorts de una signatura S₁ y de escribir cada símbolo de función
   de S₀ como composición de símbolos de S₁, entonces a partir
   de un álgebra de S₁ podemos obtener un álgebra de S₀. -}

open Signature


data SigExpr (S : Signature) (ar : Arity S) : (sorts S) → Set where
  ident : (n : Fin (length ar)) → SigExpr S ar (ar ‼ n)
  fapp  : ∀ {ar'} {s} → (f : funcs S (ar' , s)) →
                        (es : VecH (sorts S) (SigExpr S ar) ar') → SigExpr S ar s


-- Transformación de una signatura S₀ en una S₁
record SigTransf (S₀ : Signature) (S₁ : Signature) : Set where
  field
    sortsT : sorts S₀ → sorts S₁
    funsT  : ∀ {ar} {s} → (f : funcs S₀ (ar , s)) →
                          SigExpr S₁ (map sortsT ar) (sortsT s) 

-- Mapeo de sorts de una signatura a otra
mapsorts : ∀ {S₀} {S₁} → (sorts S₀ → sorts S₁) →
             SType S₀ → SType S₁
mapsorts fₛ = pmap (map fₛ) fₛ


open SigTransf
open Algebra
open Setoid


mutual
  interpSigExpr : ∀ {l₀} {l₁} {S : Signature} {ar : Arity S} →
                    (a : Algebra {l₀} {l₁} S) →
                    (vs : VecH (sorts S) (Carrier ∘ isorts a) ar) →
                    (s : sorts S) → (e : SigExpr S ar s) → 
                    (Carrier ∘ isorts a) s
  interpSigExpr a vs ._ (ident n) = vs ‼v n
  interpSigExpr a vs s (fapp {ar' = ar'} {s = .s} f es) =
                        ifuns a (ar' , s) f (mapvec a vs es)

  mapvec :  ∀ {l₀} {l₁} {S : Signature} {ar ar' : Arity S} →
              (a : Algebra {l₀} {l₁} S) → (vs : VecH (sorts S) (Carrier ∘ isorts a) ar) →
              (es : VecH (sorts S) (SigExpr S ar) ar') → VecH (sorts S) (Carrier ∘ isorts a) ar'
  mapvec {ar' = []} a vs ⟨⟩ = ⟨⟩
  mapvec {ar' = s ∷ ar₁} a vs (e ▹ es) = (interpSigExpr a vs s e) ▹ mapvec a vs es 

-- mapvec es igual a mapV interpSigExpr. Si el chequeador de terminación
-- de agda fuera más copado, no debería hacer esto.
mapvec≡mapVi : ∀ {l₀} {l₁} {S : Signature} {ar ar' : Arity S} →
                 (a : Algebra {l₀} {l₁} S) →
                 (vs : VecH (sorts S) (Carrier ∘ isorts a) ar) →
                 (es : VecH (sorts S) (SigExpr S ar) ar') → 
                 mapvec a vs es ≡ mapV (interpSigExpr a vs) ar' es
mapvec≡mapVi a vs ⟨⟩ = PE.refl
mapvec≡mapVi {ar' = s ∷ ar'} a vs (e ▹ es) =
                    PE.cong (λ es' → interpSigExpr a vs s e ▹ es')
                                     (mapvec≡mapVi a vs es) 



interpFunTrans : ∀ {l₀ l₁} (S₀ S₁ : Signature) →
                 {ar : Arity S₀} {s : sorts S₀} {fₛ : sorts S₀ → sorts S₁} →
                 (f : funcs S₀ (ar , s)) → (e : SigExpr S₁ (map fₛ ar) (fₛ s)) →
                 (a : Algebra {l₀} {l₁} S₁) → 
                 IFun S₀ (ar , s) (Carrier ∘ (isorts a ∘ fₛ))
interpFunTrans S₀ S₁ {ar} {s} {fₛ} f e a vs =
                     interpSigExpr a (vecTransf fₛ (Carrier ∘ isorts a) ar vs) (fₛ s) e 

funAlgTransf : ∀ {l₀ l₁} {S₀ S₁} (t : SigTransf S₀ S₁) →
                 (a : Algebra {l₀} {l₁} S₁) →
                 (ty : SType S₀) → (f : funcs S₀ ty) →
                 IFun S₀ ty (Carrier ∘ (isorts a ∘ sortsT t))
funAlgTransf {S₀ = S₀} {S₁ = S₁} t a (ar , s) f vs =
                   interpFunTrans S₀ S₁ f (funsT t f) a vs



p : ∀ {l₀} {l₁} {S₁} {ar : Arity S₁} {s : sorts S₁} →
    (a : Algebra {l₀} {l₁} S₁) → (e : SigExpr S₁ ar s) →
    (ts₁ ts₂ : VecH (sorts S₁) (Carrier ∘ isorts a) ar) →
    _∼v_ {R = _≈_ ∘ isorts a} ts₁ ts₂ →
    _≈_ (isorts a s) (interpSigExpr a ts₁ s e)
                     (interpSigExpr a ts₂ s e)
p a (ident n) ts₁ ts₂ eq  = ~v‼prop ts₁ ts₂ eq n
p {S₁ = S₁} {ar = ar} a (fapp {ar'} f vs) ts₁ ts₂ eq =
        ifuncong a (mapvec a ts₁ vs) (mapvec a ts₂ vs)
                   (≈mapvec ar' vs)
  where ≈mapvec : (ar' : Arity S₁) → (ws : VecH (sorts S₁) (SigExpr S₁ ar) ar') →
                  (mapvec a ts₁ ws) ∼v (mapvec a ts₂ ws)
        ≈mapvec [] ⟨⟩ = ∼⟨⟩
        ≈mapvec (s ∷ ar₁) (w ▹ ws) = ∼▹ (p a w ts₁ ts₂ eq) (≈mapvec ar₁ ws)

congTransf : ∀ {l₀} {l₁} {S₀} {S₁} {ar : Arity S₀} {s : sorts S₀}
             {f : funcs S₀ (ar , s)}→
            (t : SigTransf S₀ S₁) → (a : Algebra {l₀} {l₁} S₁) → 
            (ts₁ ts₂ : VecH (sorts S₀) (Carrier ∘ isorts a ∘ sortsT t) ar) →
            _∼v_ {R = _≈_ ∘ isorts a ∘ sortsT t} ts₁ ts₂ → 
            _≈_ (isorts a $ sortsT t s)
                (funAlgTransf t a (ar , s) f ts₁)
                (funAlgTransf t a (ar , s) f ts₂)
congTransf {S₀ = S₀} {S₁} {ar} {s} {f} t a ts₁ ts₂ ts₁≈ts₂ =
               p a (funsT t f) (vecTransf (sortsT t) (Carrier ∘ isorts a) ar ts₁)
                               (vecTransf (sortsT t) (Carrier ∘ isorts a) ar ts₂)
                               (∼vtransf (sortsT t) ts₁ ts₂ ts₁≈ts₂)

-- Transformación de un álgebra de S₁ en una de S₀
AlgTransf : ∀ {l₀} {l₁} {S₀} {S₁} → (t : SigTransf S₀ S₁) →
            (a : Algebra {l₀} {l₁} S₁) → Algebra {l₀} {l₁} S₀
AlgTransf t a = record { isorts   = isorts a ∘ sortsT t
                       ; ifuns    = λ ty f vs → funAlgTransf t a ty f vs
                       ; ifuncong = congTransf t a
                       }

open Homomorphism



presTransf' : ∀ {l₀ l₁} {S₁ : Signature} {a a' : Algebra {l₀} {l₁} S₁}
                (h : Homomorphism S₁ a a') →
                (ar : Arity S₁) → (s : sorts S₁) →
                (e : SigExpr S₁ ar s) → (vs : VecH (sorts S₁) (Carrier ∘ isorts a) ar) →
                _≈_ (isorts a' s)
                    (morph h s ⟨$⟩ interpSigExpr a vs s e)
                    (interpSigExpr a' (mapMorph {A = a} {A' = a'}
                                                (morph h) vs) s e)
presTransf' h .[] ._ (ident ()) ⟨⟩
presTransf' {a' = a'} h (s ∷ ar) .s (ident zero) (v ▹ vs) = Setoid.refl (isorts a' s)
presTransf' h (s ∷ ar) ._ (ident (suc n)) (x ▹ vs) = presTransf' h ar (ar ‼ n) (ident n) vs
presTransf' {S₁ = S₁} {a} {a'} h ar s (fapp {ar' = ar'} f es) vs =
                           Setoid.trans (isorts a' s)
                                        (preserv h (ar' , s) f (mapvec a vs es))
                                        (ifuncong a' {f = f} (mapMorph {A = a} {A' = a'}
                                                                       (morph h) (mapvec a vs es))
                                                             (mapvec a' (mapMorph {A = a} {A' = a'}
                                                                                  (morph h) vs) es)
                                                             (presVec ar' es))
  where presVec : (ar₀ : Arity S₁) →
                  (es₀ : VecH (sorts S₁) (SigExpr S₁ ar) ar₀) →
                  mapMorph {A = a} {A' = a'} (morph h) (mapvec a vs es₀) ∼v
                  mapvec a' (mapMorph {A = a} {A' = a'} (morph h) vs) es₀
        presVec [] ⟨⟩ = ∼⟨⟩
        presVec (s₁ ∷ ar₁) (e ▹ es₀) = ∼▹ (presTransf' h ar s₁ e vs)
                                          (presVec ar₁ es₀)



presTransf : ∀ {l₀ l₁} {S₀ S₁ : Signature} {a a' : Algebra {l₀} {l₁} S₁} →
                       (t : SigTransf S₀ S₁) → (h : Homomorphism S₁ a a') →
                       (ty : SType S₀) → (f : funcs S₀ ty) →
                       homPreserv S₀ (AlgTransf t a) (AlgTransf t a')
                                     (morph h ∘ sortsT t) ty f
presTransf {S₀ = S₀} {S₁} {a} {a'} t h (ar , s) f as =
                          subst (λ vec → _≈_ (isorts a' (sortsT t s))
                                             (_⟨$⟩_ (morph h (sortsT t s))
                                                (interpSigExpr a (vecTransf (sortsT t) (Carrier ∘ isorts a) ar as)
                                                 (sortsT t s) (funsT t f)))
                                                 (interpSigExpr a' vec (sortsT t s) (funsT t f)))
                                (≡maptransf (sortsT t) (Carrier ∘ isorts a)
                                                (Carrier ∘ isorts a') (_⟨$⟩_ ∘ morph h) ar as)
                                (presTransf' h (map (sortsT t) ar) (sortsT t s) (funsT t f)
                                               (vecTransf (sortsT t) (Carrier ∘ isorts a) ar as))

{- Si tenemos un homomorfismo entre álgebras de S₁ y tenemos
   una transformación de S₀ en S₁, entonces podemos obtener
   un homomorfismo entre las álgebras transformadas de S₀ -}
HomTransf : ∀ {l₀ l₁} {S₀ S₁ : Signature} {a a' : Algebra {l₀} {l₁} S₁} →
              (t : SigTransf S₀ S₁) → (h : Homomorphism S₁ a a') →
              Homomorphism S₀ (AlgTransf t a) (AlgTransf t a')
HomTransf t h = record { morph = morph h ∘ sortsT t
                       ; preserv = presTransf t h }
           
