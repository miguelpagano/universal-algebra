module UnivAlgebra where

open import Relation.Binary
open import Level renaming (suc to lsuc)
open import Data.Nat hiding (_⊔_)
open import Data.Vec
open import Data.Product hiding (map)
open import Function

mkFun : ∀ {l} {n} → Vec (Set l) n → Set l → Set l
mkFun [] A = A
mkFun (x ∷ xs) A = x → mkFun xs A


open Setoid

record Signature {l₁ l₂ l₃ l₄ : Level} : Set (lsuc (l₁ ⊔ l₂ ⊔ l₃ ⊔ l₄)) where
  field
    sorts : Setoid l₁ l₂
    funcs : Setoid l₃ l₄
    -- Aridad. Para cada símbolo de función obtenemos la cantidad de 
    -- parámetros y su tipo.
    arity : Carrier funcs → Σ ℕ (λ n → Vec (Carrier sorts) (suc n))


open Signature

record Algebra {l₁ l₂ l₃ l₄ : Level} (S : Signature {l₁} {l₂} {l₃} {l₄}) : 
                                   Set (lsuc (l₁ ⊔ l₂ ⊔ l₃ ⊔ l₄)) where
  field
    isorts   : (s : Carrier (sorts S)) → Setoid l₁ l₂ -- No se qué nivel deberia ir aqui
    ifuns    : (f : Carrier (funcs S)) → 
                    mkFun {l₁} {proj₁ $ arity S f} 
                               (map (Carrier ∘ isorts) $ tail $ proj₂ $ arity S f)
                               (Carrier $ isorts $ head $ proj₂ $ arity S f)
                                               

record Homomorphism {l₁ l₂ l₃ l₄ : Level} 
                    (S : Signature {l₁} {l₂} {l₃} {l₄}) (A A' : Algebra S) : 
                                   Set (lsuc (l₁ ⊔ l₂ ⊔ l₃ ⊔ l₄)) where
  open Algebra
  field
    -- Familia de funciones
    morphs  : (s : Carrier (sorts S)) → Carrier (isorts A s) → 
                                        Carrier (isorts A' s)
    -- Propiedad de preservación de operaciones. Parece que necesitamos
    -- vectores heterogéneos.
    -- preserv : (f : Carrier (funcs S)) → (as : Vec 