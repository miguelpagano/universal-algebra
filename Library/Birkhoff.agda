-- Universal Algebra Library
--
-- Models of semi-equational theories are closed under ISP.
-- Models of equational theories are closde under IHSP.
--
open import UnivAlgebra
open import TermAlgebra
module Birkhoff {Σ : Signature} where

open import Data.List using (List;[])
open import Data.Product hiding (Σ;map)
open import Function.Bijection using (Bijective)
open import Function
open import Function.Equality hiding (_∘_)
open import Relation.Binary
import Relation.Binary.EqReasoning as EqR

open import Equational Σ
open import HeterogeneousVec
open import Morphisms
open import Product

open OpenTerm Σ renaming (T_〔_〕 to TΣ〔_〕)

open HomComp
open Equation

open Hom
open Homo

private
  Terms : ∀ X s → Set _
  Terms X s = TΣ〔 X 〕 ∥ s ∥


module aux-sem {ℓ₀ ℓ₁ ℓ₂ ℓ₃}
  (X : Vars Σ)
  (A : Algebra {ℓ₀} {ℓ₁} Σ) (B : Algebra {ℓ₂} {ℓ₃} Σ)
  (θB : Env X B) (H : Homo B A) where
  θA : Env X A
  θA {s} x = ′ H ′ s ⟨$⟩ θB x


  module EB = Eval X B θB renaming (TΣXHom to TΣB;⟦_⟧ to ⟦_⟧B)
  module EA = Eval X A θA renaming (TΣXHom to TΣA;⟦_⟧ to ⟦_⟧A)
  open EvalUMP X A θA
  open EA
  open EB
  open EB using (⟦_⟧B) public
  open EA using (⟦_⟧A) public
  _,_≈A_ : (s : sorts Σ) → _
  _,_≈A_ s = Setoid._≈_ (A ⟦ s ⟧ₛ)

  _,_≈B_ : (s : sorts Σ) → _
  _,_≈B_ s = Setoid._≈_ (B ⟦ s ⟧ₛ)

  ⟦t⟧A≈H⟦t⟧B : ∀ {s : sorts Σ} → (t : Terms X s) →
               s , ⟦ t ⟧A ≈A ( ′ H ′ s ⟨$⟩ ⟦ t ⟧B)
  ⟦t⟧A≈H⟦t⟧B {s} t = UMP TΣA (H ∘ₕ TΣB)
                        (λ {s'} _ → Setoid.refl (A ⟦ s' ⟧ₛ))
                        (λ {s'} _ → Setoid.refl (A ⟦ s' ⟧ₛ))
                        s t
  open Equ
  ≈B→≈A : ∀ {s : sorts Σ} (eq : Equ X s ) →
            let t ≈ₑ t' = eq
            in
            s , ⟦ t ⟧B ≈B ⟦ t' ⟧B → s , ⟦ t ⟧A ≈A ⟦ t' ⟧A
  ≈B→≈A {s} (t ≈ₑ t') eq = begin
    ⟦ t ⟧A               ≈⟨ ⟦t⟧A≈H⟦t⟧B t ⟩
    ′ H ′ s ⟨$⟩ ⟦ t ⟧B    ≈⟨ cong (′ H ′ s ) eq ⟩
    ′ H ′ s ⟨$⟩ ⟦ t' ⟧B   ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (⟦t⟧A≈H⟦t⟧B t')  ⟩
    ⟦ t' ⟧A ∎
    where open EqR (A ⟦ s ⟧ₛ)

  open Setoid

  ⊨B*→⊨A* : ∀ {ar : List (sorts Σ)} {eqs : HVec (Equ X) ar } →
           (B , θB ⊨ₑ_ ) ⇨v eqs →
           (A , θA ⊨ₑ_) ⇨v eqs
  ⊨B*→⊨A* B⊨conds = map⇨v (λ {_} {eq} → ≈B→≈A eq ) B⊨conds


{- Isomorphisms of algebras preserve satisfaction of conditional equations -}
module IsoRespectSatisfaction
  {ℓ₀ ℓ₁ ℓ₂ ℓ₃} {s : sorts Σ} (e : Equation s)
  {A : Algebra {ℓ₀} {ℓ₁} Σ} {B : Algebra {ℓ₂} {ℓ₃} Σ}
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
   ⟦ right e ⟧B  ∎
     where
     open EqR (B ⟦ s ⟧ₛ)
     open Setoid (B ⟦ s ⟧ₛ)
     open aux-sem (X e) A B θB homBA
     symA : _ → _
     symA = Setoid.sym (A ⟦ s ⟧ₛ)


{- Sub-algebras preserve satisfaction of conditional equations -}
module SubAlgebrasRespectSatisfaction
       {ℓ₃} {ℓ₁ ℓ₂} {s : sorts Σ} (e : Equation s)
       (A : Algebra {ℓ₁} {ℓ₂} Σ) (B≤A : SubAlg {ℓ₃} A) (A⊨e : A ⊨ e)
       where

  SubRespects⊨ : SubAlgebra B≤A ⊨ e
  SubRespects⊨ θB B⊨conds = begin
    proj₁ ⟦ left e ⟧B   ≈⟨ sym (⟦t⟧A≈H⟦t⟧B (left e)) ⟩
    ⟦ left e ⟧A         ≈⟨ A⊨e θA (⊨B*→⊨A* B⊨conds) ⟩
    ⟦ right e ⟧A        ≈⟨ ⟦t⟧A≈H⟦t⟧B (right e) ⟩
    proj₁ ⟦ right e ⟧B ∎
    where
    open aux-sem (X e) A (SubAlgebra B≤A) θB (sub-embedding A B≤A)
    open EqR (A ⟦ s ⟧ₛ)
    open Setoid (A ⟦ s ⟧ₛ)

module ProductRespectSatisfaction
       {ℓ₁ ℓ₂ ℓ₃} {s : sorts Σ} (e : Equation s)
       {I : Set ℓ₁} (A : I → Algebra {ℓ₂} {ℓ₃} Σ)
         (Ai⊨e : (i : I) → A i ⊨ e) where
  open IndexedProduct {I = I} A

  Πalg⊨ : Πalg ⊨ e
  Πalg⊨ θ Π⊨conds i =  begin
    ′ π i ′ s ⟨$⟩ ⟦ left e ⟧B    ≈⟨ sym (⟦t⟧A≈H⟦t⟧B (left e)) ⟩
    ⟦ left e ⟧A                 ≈⟨ Ai⊨e i θA (⊨B*→⊨A* Π⊨conds) ⟩
    ⟦ right e ⟧A                ≈⟨ ⟦t⟧A≈H⟦t⟧B (right e) ⟩
   ′ π i ′ s ⟨$⟩ ⟦ right e ⟧B ∎
   where
   open EqR (A i ⟦ s ⟧ₛ)
   open Setoid (A i ⟦ s ⟧ₛ)
   open aux-sem (X e) (A i) Πalg θ (π i)

{- Quotients preserve equations -}
module QuotientPreserveSatisfaction
  {ℓ₀ ℓ₁ ℓ₂}  {s : sorts Σ} {X : Vars Σ} (e : Equ X s)
  (A : Algebra {ℓ₀} {ℓ₁} Σ) (φ : Congruence {ℓ₂} A)
   (A⊨e : A ⊨ equ-to-Equation X s e) where

   A/φ : _
   A/φ = A / φ
   ν : Homo A (A / φ)
   ν = QuotHom A φ

   t : Terms X s
   t' : Terms X s
   t = Equ.eleft e
   t' = Equ.eright e

   A/φ⊨e : A/φ ⊨ equ-to-Equation X s e
   A/φ⊨e θk ⇨v⟨⟩ = begin
     ⟦ t ⟧A              ≈⟨ ⟦t⟧A≈H⟦t⟧B t ⟩
     ′ ν ′ s ⟨$⟩ ⟦ t ⟧B   ≈⟨ Π.cong (′ ν ′ s) (A⊨e θA ⇨v⟨⟩) ⟩
     ′ ν ′ s ⟨$⟩ ⟦ t' ⟧B  ≈⟨ sym (⟦t⟧A≈H⟦t⟧B t') ⟩
     ⟦ t' ⟧A ∎
     where
     open EqR (A/φ ⟦ s ⟧ₛ)
     open Setoid (A/φ ⟦ s ⟧ₛ)
     open aux-sem {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₂} {ℓ₂ = ℓ₀} {ℓ₃ = ℓ₁} X A/φ A θk ν


{- Homomorphic images preserve equations -}
module HomImgRespectSatisfaction
  {ℓ₀ ℓ₁ ℓ₂ ℓ₃}  {s : sorts Σ} {X : Vars Σ} (e : Equ X s)
  (A : Algebra {ℓ₀} {ℓ₁} Σ) (B : Algebra {ℓ₂} {ℓ₃} Σ)
  (H : Homo A B) (A⊨e : A ⊨ equ-to-Equation X s e) where

   A/h : _
   A/h = A / Kernel H
   ν : Homo A (A / Kernel H)
   ν = QuotHom A (Kernel H)

   import IsoTheorems as I

   equ : Equation s
   equ = (⋀ X , Equ.eleft e ≈ Equ.eright e)

   imgH⊨e : homImg A H ⊨ equ
   imgH⊨e = IsoRespects⊨ (A/φ⊨e A⊨e)
     where open IsoRespectSatisfaction equ (I.iso-A/kerH A B H)
           open QuotientPreserveSatisfaction e A (Kernel H)

module ModSemiEquationIsISP  {ar} (E : Theory ar) where

  isoClosed : ∀ {ℓ₀ ℓ₁ ℓ₂ ℓ₃} (A : Algebra  {ℓ₀} {ℓ₁} Σ) → A ⊨T E →
               (B : Algebra  {ℓ₂} {ℓ₃} Σ) → A ≅ B → B ⊨T E
  isoClosed A A⊨E B iso {e = e} e∈E = IsoRespects⊨ (A⊨E e∈E)
    where open IsoRespectSatisfaction e iso


  subClosed : ∀ {ℓ₀ ℓ₁ ℓ₂} (A : Algebra  {ℓ₀} {ℓ₁} Σ) → A ⊨T E →
               (B : SubAlg {ℓ₂} A) → SubAlgebra B ⊨T E
  subClosed A A⊨E B {e = e} e∈E = SubRespects⊨ (A⊨E e∈E)
    where open SubAlgebrasRespectSatisfaction e A B

  open IndexedProduct
  prodClosed : ∀ {ℓ₀ ℓ₁ ℓ₂} {I : Set ℓ₀}
               (A : I → Algebra  {ℓ₁} {ℓ₂} Σ) →
               (∀ i → A i ⊨T E) → Πalg A ⊨T E
  prodClosed A Ai⊨E {e = e} e∈E = Πalg⊨ (λ i → Ai⊨E i e∈E)
    where open ProductRespectSatisfaction e A


  open ProdAlg
  binProdClosed : ∀ {ℓ₀ ℓ₁} (A B : Algebra  {ℓ₀} {ℓ₁} Σ) →
               A ⊨T E → B ⊨T E →
               (A ×-alg B) ⊨T E
  binProdClosed A B A⊨E B⊨E = isoClosed ΠAB ΠAB⊨E (A ×-alg B) A×B≅Π
    where
    open BinaryProduct A B renaming (Πalg to ΠAB)
    open import Morphisms
    open import Data.Bool
    open _≅_
    A×B≅Π = record { iso = symIso (A ×-alg B) ΠAB iso×-2→ }
    Ai⊨E : (i : Bool) → Ai i ⊨T E
    Ai⊨E false = B⊨E
    Ai⊨E true = A⊨E
    ΠAB⊨E : ΠAB ⊨T E
    ΠAB⊨E = prodClosed Ai Ai⊨E


module ModEquationIsIHSP  {ar} {X : Vars Σ} (T : EqTheory X ar) where

  E : Theory ar
  E = eqTheory-to-Theory T
  open import Relation.Binary.PropositionalEquality using (_≡_)

  module ISP = ModSemiEquationIsISP E

  isoClosed : ∀ {ℓ₀ ℓ₁ ℓ₂ ℓ₃} (A : Algebra  {ℓ₀} {ℓ₁} Σ) → A ⊨T E →
               (B : Algebra  {ℓ₂} {ℓ₃} Σ) → A ≅ B → B ⊨T E
  isoClosed = ISP.isoClosed


  subClosed : ∀ {ℓ₀ ℓ₁ ℓ₂} (A : Algebra {ℓ₀} {ℓ₁} Σ) → A ⊨T E →
               (B : SubAlg {ℓ₂} A) → SubAlgebra B ⊨T E
  subClosed = ISP.subClosed


  open IndexedProduct
  prodClosed : ∀ {ℓ₀ ℓ₁ ℓ₂} {I : Set ℓ₀}
               (A : I → Algebra  {ℓ₁} {ℓ₂} Σ) →
               (∀ i → A i ⊨T E) → Πalg A ⊨T E
  prodClosed = ISP.prodClosed

  {- We should change the definition of Equation -}
  himgClosed : ∀ {ℓ₀ ℓ₁ ℓ₂ ℓ₃} (A : Algebra  {ℓ₀} {ℓ₁} Σ) →
               (B : Algebra  {ℓ₂} {ℓ₃} Σ) →(h : Homo A B) →
               ∀ {s} {e} → e ∈ T → A ⊨ (equ-to-Equation X s e) →
               homImg A h ⊨ (equ-to-Equation X s e)
  himgClosed A B h {s = s} {e = e} e∈E A⊨e = imgH⊨e A⊨e
    where open HomImgRespectSatisfaction e A B h
