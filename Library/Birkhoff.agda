open import UnivAlgebra
open import Equational
module Birkhoff {Σ : Signature} {X : Vars Σ} where
open Signature 
open import Variety
open import Morphisms
open import HeterogeneousVec

open import Data.Product hiding (Σ;map)
open import Function.Bijection  hiding (_∘_)
open import Function.Surjection hiding (_∘_)
open import Function hiding (module Bijection;Bijection;Bijective)
open import Function.Equality hiding (_∘_)
open import Relation.Binary
import Relation.Binary.EqReasoning as EqR
open Algebra
open Signature
open import Setoids using (∥_∥)

open import TermAlgebra (Σ 〔 X 〕) hiding (∣T∣)
open import TermAlgebra
open HomComp
open Equation

open Hom
open Homo



module aux-sem {ℓ₀ ℓ₁ ℓ₂ ℓ₃} 
  (A : Algebra {ℓ₀} {ℓ₁} Σ) (B : Algebra {ℓ₂} {ℓ₃} Σ)
  (θB : Env X B) (H : Homo B A) where
  θA : Env X A
  θA {s} x = ′ H ′ s ⟨$⟩ θB x

  Terms : ∀ s → Set _
  Terms s = ∥ ∣T∣ (Σ 〔 X 〕) ⟦ s ⟧ₛ ∥

  open InitHomoExt B θB renaming (TΣXHom to TΣB) hiding (tot)
  open InitHomoExt A θA renaming (TΣXHom to TΣA)
     
  open EnvExt X A renaming (_↪ to _↪A)
  open EnvExt X B renaming (_↪ to _↪B)
  
  _,_≈A_ : (s : sorts Σ) → _
  _,_≈A_ s = Setoid._≈_ (A ⟦ s ⟧ₛ)

  ⟦_⟧A : ∀ {s : sorts Σ} → Terms s → ∥ A ⟦ s ⟧ₛ ∥
  ⟦_⟧A {s} = θA ↪A 

  _,_≈B_ : (s : sorts Σ) → _
  _,_≈B_ s = Setoid._≈_ (B ⟦ s ⟧ₛ)

  ⟦_⟧B : ∀ {s : sorts Σ} → Terms s → ∥ B ⟦ s ⟧ₛ ∥
  ⟦_⟧B {s}  = θB ↪B

  ⟦t⟧A≈H⟦t⟧B : ∀ {s : sorts Σ} → (t : Terms s) →
                 s , ⟦ t ⟧A ≈A ( ′ H ′ s ⟨$⟩ ⟦ t ⟧B)
  ⟦t⟧A≈H⟦t⟧B {s} t = tot TΣA (H ∘ₕ TΣB)
                        (λ s' _ → Setoid.refl (A ⟦ s' ⟧ₛ))
                        (λ s' _ → Setoid.refl (A ⟦ s' ⟧ₛ))
                        s t

  ≈B→≈A : ∀ {s : sorts Σ} {t t' : ∥ ∣T∣ (Σ 〔 X 〕) ⟦ s ⟧ₛ ∥ } →
           (s , ⟦ t ⟧B ≈B ⟦ t' ⟧B) → (s , ⟦ t ⟧A ≈A ⟦ t' ⟧A)
  ≈B→≈A {s} {t} {t'} eq = begin
                         ⟦ t ⟧A
                         ≈⟨ ⟦t⟧A≈H⟦t⟧B t ⟩
                         ′ H ′ s ⟨$⟩ ⟦ t ⟧B
                         ≈⟨ cong (′ H ′ s ) eq ⟩
                         ′ H ′ s ⟨$⟩ ⟦ t' ⟧B
                         ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (⟦t⟧A≈H⟦t⟧B t')  ⟩
                         ⟦ t' ⟧A
                         ∎
              where open EqR (A ⟦ s ⟧ₛ)

  open import Data.List using (List)
  open Setoid
  
  rA : ∀ s → Rel (Terms s) ℓ₁
  rA sᵢ uᵢ uᵢ' = _≈_ (A ⟦ sᵢ ⟧ₛ) ⟦ uᵢ ⟧A ⟦ uᵢ' ⟧A

  rB : ∀ s → Rel (Terms s) ℓ₃
  rB sᵢ uᵢ uᵢ' = _≈_ (B ⟦ sᵢ ⟧ₛ) ⟦ uᵢ ⟧B ⟦ uᵢ' ⟧B
  
  ⊨B*→⊨A* : ∀ {ar : List (sorts Σ)} {ts ts' : HVec Terms ar } →
           _∼v_ {R = rB} ts ts' →
           _∼v_ {R = rA } ts ts'
  ⊨B*→⊨A* B⊨conds = map∼v (λ {s'} {t} {t'} eq → ≈B→≈A {s'} {t} {t'} eq) B⊨conds


{- Isomorphisms of algebras preserve satisfaction of equations -}
module IsoRespectModel
  {ℓ₀ ℓ₁ ℓ₂ ℓ₃} {s : sorts Σ} (e : Equation Σ X s)
  (A : Algebra {ℓ₀} {ℓ₁} Σ) (B : Algebra {ℓ₂} {ℓ₃} Σ) 
  (A≅B : A ≅ B) (A⊨e : A ⊨ e)
  where
  open Isomorphism
  open HomComp
  open _≅_
  open Bijective

  isoAB : Isomorphism A B
  isoAB = iso A≅B

  homAB : Homo A B
  homAB = hom isoAB

  homBA : Homo B A
  homBA = hom (symIso A B isoAB)

  IsoRespects⊨ : B ⊨ e
  IsoRespects⊨ θB B⊨conds = begin
       ⟦ left e ⟧B
      ≈⟨ iso-≈ isoAB s ⟦ left e ⟧B ⟩
      ′ homAB ∘ₕ homBA ′ s ⟨$⟩ ⟦ left e ⟧B
      ≈⟨ Π.cong (′ homAB ′ s) (symA (⟦t⟧A≈H⟦t⟧B (left e))) ⟩
      ′ homAB ′ s ⟨$⟩ ⟦ left e ⟧A
      ≈⟨ Π.cong (′ homAB  ′ s) (A⊨e θA (⊨B*→⊨A* B⊨conds)) ⟩
      ′ homAB ′ s ⟨$⟩ ⟦ right e ⟧A
      ≈⟨ Π.cong (′ homAB ′ s) (⟦t⟧A≈H⟦t⟧B (right e)) ⟩
      ′ homAB ∘ₕ homBA ′ s ⟨$⟩ ⟦ right e ⟧B
      ≈⟨ sym (iso-≈ isoAB s ⟦ right e ⟧B)  ⟩
      ⟦ right e ⟧B
      ∎
    where
      open EqR (B ⟦ s ⟧ₛ) 
      open Setoid (B ⟦ s ⟧ₛ)
      open aux-sem A B θB homBA
      symA : _ → _
      symA = Setoid.sym (A ⟦ s ⟧ₛ)


{- Sub-algebras preserve satisfaction of equations -}
module SubAlgebra-Preserve-⊨
       {ℓ₃} {ℓ₁ ℓ₂} {s : sorts Σ} (e : Equation Σ X s)
       (A : Algebra {ℓ₁} {ℓ₂} Σ) (A⊨e : A ⊨ e) (B≤A : SubAlg {ℓ₃} A)
       where
     
  SubRespects⊨ : SubAlgebra B≤A ⊨ e
  SubRespects⊨ θB B⊨conds = begin
        proj₁ ⟦ left e ⟧B
        ≈⟨ sym (⟦t⟧A≈H⟦t⟧B (left e)) ⟩
        ⟦ left e ⟧A
        ≈⟨ A⊨e θA (⊨B*→⊨A* B⊨conds) ⟩
        ⟦ right e ⟧A
        ≈⟨ ⟦t⟧A≈H⟦t⟧B (right e) ⟩
        proj₁ ⟦ right e ⟧B
        ∎
        where open EqR (A ⟦ s ⟧ₛ) 
              open Setoid (A ⟦ s ⟧ₛ)
              open aux-sem A (SubAlgebra B≤A) θB (Canonical A B≤A)

module Product-Preserve-⊨
       {ℓ₁ ℓ₂ ℓ₃} {s : sorts Σ} (e : Equation Σ X s)
       {I : Set ℓ₁} {A : I → Algebra {ℓ₂} {ℓ₃} Σ}
         (Ai⊨e : (i : I) → A i ⊨ e) where
  open import Product
  open IndexedProduct {I = I} A 
  
  Πalg⊨e : Πalg ⊨ e
  Πalg⊨e θ Π⊨conds i =  begin
                     ′ π i ′ s ⟨$⟩ ⟦ left e ⟧B
                        ≈⟨ sym (⟦t⟧A≈H⟦t⟧B (left e)) ⟩
                      ⟦ left e ⟧A
                        ≈⟨ Ai⊨e i θA (⊨B*→⊨A* Π⊨conds) ⟩
                      ⟦ right e ⟧A
                        ≈⟨ ⟦t⟧A≈H⟦t⟧B (right e) ⟩
                      ′ π i ′ s ⟨$⟩ ⟦ right e ⟧B
                          ∎
         where open EqR (A i ⟦ s ⟧ₛ)
               open Setoid (A i ⟦ s ⟧ₛ)
               open aux-sem (A i) Πalg θ (π i)
   
{- Proposition 2.2.8 (Part 'if' of Birkhoff theorem) -}
prop : ∀ {ℓ₀} {Σ} → (C : AlgClass {ℓ₀} {ℓ₀} Σ) → EqDefClass {ℓ₀} {ℓ₀} Σ C →
                     Variety {ℓ₀} Σ C
prop C eqc = {!!}
