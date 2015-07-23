module Ejemplos.Monoides where

open import UnivAlgebra
open import Relation.Binary
import Relation.Binary.Indexed.Core 
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Nat hiding (_⊔_)
open import Data.Product hiding (map)
open import Function
open import Function.Equality hiding (setoid;_∘_;cong) 
open import Data.Unit hiding (setoid)
open import Data.Bool
open import Relation.Binary.PropositionalEquality

data Sort : Set where
  S : Sort
      
data FunM : Set where
  unit : FunM
  mult : FunM
         
arFunM : FunM → NProd Sort × Sort
arFunM unit = (0 , lift unit) , S
arFunM mult = (2 , (S , S )) , S

open Signature
open Setoid
open Algebra

monSig : Signature
monSig = record { sorts = Sort
                ; funcs = FunM
                ; arity = arFunM
                }
                  
-- Algunos monoides: 1. el monoide aditivo de los naturales.
PlusMon : Algebra monSig
PlusMon = record { isorts = monSort
                 ; ifuns = monFun
                 }
        where monSort : sorts monSig → Setoid lzero lzero
              monSort S = setoid ℕ
              
              monFun :  (f : funcs monSig) → IFun {monSig} (arity monSig f) (Carrier ∘ monSort)
              monFun unit x = 0
              monFun mult (m , n) = m + n
                                        
-- 2. el monoide de listas (de naturales, podría ser polimórfico)
open import Data.List
ListMon : Algebra monSig
ListMon = record { isorts = monSort
                 ; ifuns = monFun
                 }
        where monSort : sorts monSig → Setoid lzero lzero
              monSort S = setoid (List ℕ)
               
              monFun :  (f : funcs monSig) → IFun {monSig} (arity monSig f) (Carrier ∘ monSort)
              monFun unit x = []
              monFun mult (ls , ls') = ls Data.List.++ ls'
                                                       
                                                       
-- 3. el monoide trivial
UnitMon : Algebra monSig
UnitMon = record { isorts = unitSort
                 ; ifuns = unitFun
                 }
          where unitSort : sorts monSig → Setoid lzero lzero
                unitSort S = setoid Unit
          
                unitFun :  (f : funcs monSig) → IFun {monSig} (arity monSig f) (Carrier ∘ unitSort)
                unitFun unit x = unit
                unitFun mult x = unit

-- 4. 2 con ∨
OrMon : Algebra monSig
OrMon = record { isorts = orSort
               ; ifuns = orFun
               }
        where orSort : sorts monSig → Setoid lzero lzero
              orSort S = setoid Bool
                    
              orFun : (f : funcs monSig) → IFun {monSig} (arity monSig f) (Carrier ∘ orSort)
              orFun unit _ = false
              orFun mult (b , b') = b ∨ b'
                    

-- Algunos homomorfismos: 1. el terminal.
trivialHomo : (A : Algebra monSig) → Homomorphism monSig A UnitMon
trivialHomo A = record { morph = morph
                       ; preserv = pres
                       }
            where morph : (s : sorts monSig) → (isorts A s) ⟶ (isorts UnitMon s)
                  morph S = record { _⟨$⟩_ = λ x → unit
                                   ; cong = λ {i} {j} _ → _≡_.refl
                                   }

                  pres : (f : funcs monSig) → homPreserv monSig A UnitMon morph f
                  pres unit = λ as → _≡_.refl
                  pres mult as = _≡_.refl
                    
-- -- 2. El que mapea listas a su longitud.
listToNat : Homomorphism monSig ListMon PlusMon 
listToNat = record { morph = morph
                   ; preserv = pres }

          where morph : (s : sorts monSig) → (isorts ListMon s) ⟶  (isorts PlusMon s)
                morph S = record { _⟨$⟩_ = λ x → length x
                                 ; cong = λ {ls} {ls'} x → cong length x
                                 }
                lengthPlus : (l l' : List ℕ) → length (l ++ l') ≡ length l + length l'
                lengthPlus [] l' = _≡_.refl
                lengthPlus (x ∷ l) l' = cong (_+_ 1) (lengthPlus l l') -- 

                pres : (f : funcs monSig) → homPreserv monSig ListMon PlusMon morph f
                pres unit _ = _≡_.refl
                pres mult (ls , ls') = lengthPlus ls ls'

-- -- 3. isSuc

natToBool : Homomorphism monSig PlusMon OrMon
natToBool = record { morph = morph
                   ; preserv = pres
                   }
          where morph : (s : sorts monSig) → (isorts PlusMon s) ⟶ (isorts OrMon s)
                morph S = record { _⟨$⟩_ = fun ; cong = cong fun }
                  where fun : ℕ → Bool
                        fun zero = false
                        fun (suc _) = true

                pres : (f : funcs monSig) → homPreserv monSig PlusMon OrMon morph f
                pres unit x = _≡_.refl
                pres mult (zero , zero) = _≡_.refl
                pres mult (zero , suc m) = _≡_.refl
                pres mult (suc n , m) = _≡_.refl

-- -- 4. isApp

listToBool : Homomorphism monSig ListMon OrMon
listToBool = record { morph = morph
                    ; preserv = pres
                    }
           where morph : (s : sorts monSig) → (isorts ListMon s) ⟶ (isorts OrMon s)
                 morph S = record { _⟨$⟩_ = fun ; cong = cong fun }
                       where fun : List ℕ → Bool
                             fun [] = false
                             fun (_ ∷ _) = true

                 pres : (f : funcs monSig) → homPreserv monSig ListMon OrMon morph f
                 pres unit x = _≡_.refl
                 pres mult ([] , []) = _≡_.refl
                 pres mult ([] , _ ∷ _) = _≡_.refl
                 pres mult (_ ∷ _ , _) = _≡_.refl
                      
        
-- Ahora podemos probar: listToBool =  natToBool · listToNat
listToBool' : Homomorphism monSig ListMon OrMon
listToBool' = natToBool ∘ₕ listToNat

same : listToBool ≈ₕ listToBool'
same = ext listToBool listToBool' prop
  where prop : (s : sorts monSig) (a b : Carrier (isorts ListMon s)) →
               (isorts ListMon s ≈ a) b →
               (isorts OrMon s ≈ Homomorphism.morph listToBool s ⟨$⟩ a)
               (Homomorphism.morph listToBool' s ⟨$⟩ b)
        prop S [] .[] _≡_.refl = _≡_.refl
        prop S (x ∷ a) .(x ∷ a) _≡_.refl = _≡_.refl
