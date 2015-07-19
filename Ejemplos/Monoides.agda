module Ejemplos.Monoides where

open import UnivAlgebra
open import Relation.Binary
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Nat hiding (_⊔_)
open import Data.Vec
open import Data.Product hiding (map)
open import Function
open import Data.Unit hiding (setoid)
open import Data.Bool
open import Relation.Binary.PropositionalEquality

data Sort : Set where
  S : Sort
      
data FunM : Set where
  unit : FunM
  mult : FunM
         
arFunM : FunM → NProd Sort
arFunM unit = 0 , S
arFunM mult = 2 , ((S , S) , S)

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
              
              monFun :  (f : funcs monSig) → Fun (sorts monSig) (arity monSig f) (Carrier ∘ monSort)
              monFun unit = 0
              monFun mult (m , n) = m + n
                                        
-- 2. el monoide de listas (de naturales, podría ser polimórfico)
open import Data.List
ListMon : Algebra monSig
ListMon = record { isorts = monSort
                 ; ifuns = monFun
                 }
        where monSort : sorts monSig → Setoid lzero lzero
              monSort S = setoid (List ℕ)
               
              monFun :  (f : funcs monSig) → Fun (sorts monSig) (arity monSig f) (Carrier ∘ monSort)
              monFun unit = []
              monFun mult (ls , ls') = ls Data.List.++ ls'
                                                       
                                                       
-- 3. el monoide trivial
UnitMon : Algebra monSig
UnitMon = record { isorts = unitSort
                 ; ifuns = unitFun
                 }
          where unitSort : sorts monSig → Setoid lzero lzero
                unitSort S = setoid Unit
          
                unitFun :  (f : funcs monSig) → Fun (sorts monSig) (arity monSig f) (Carrier ∘ unitSort)
                unitFun unit = unit
                unitFun mult x = unit

-- 4. 2 con ∨
OrMon : Algebra monSig
OrMon = record { isorts = orSort
               ; ifuns = orFun
               }
        where orSort : sorts monSig → Setoid lzero lzero
              orSort S = setoid Bool
                    
              orFun : (f : funcs monSig) → Fun (sorts monSig) (arity monSig f) (Carrier ∘ orSort)
              orFun unit = false
              orFun mult (b , b') = b ∨ b'
                    

-- Algunos homomorfismos: 1. el terminal.
trivialHomo : (A : Algebra monSig) → Homomorphism monSig A UnitMon
trivialHomo A = record { morphs = morph
                ; preserv = pres
                  }
            where morph : (s : sorts monSig) → Carrier (isorts A s) → Carrier (isorts UnitMon s)
                  morph S x = unit

                  pres : (f : funcs monSig) → homPreserv monSig A UnitMon morph f
                  pres unit = lift _≡_.refl
                  pres mult as = _≡_.refl
                    
-- 2. El que mapea listas a su longitud.
listToNat : Homomorphism monSig ListMon PlusMon 
listToNat = record { morphs = morph
                   ; preserv = pres }

          where morph : (s : sorts monSig) → Carrier (isorts ListMon s) → Carrier (isorts PlusMon s)
                morph S ls = length ls

                lengthPlus : (l l' : List ℕ) → length (l Data.List.++ l') ≡ length l + length l'
                lengthPlus [] l' = _≡_.refl
                lengthPlus (x ∷ l) l' = cong (_+_ 1) (lengthPlus l l')

                pres : (f : funcs monSig) → homPreserv monSig ListMon PlusMon morph f
                pres unit = lift _≡_.refl
                pres mult (ls , ls') = lengthPlus ls ls'

-- 3. isSuc

natToBool : Homomorphism monSig PlusMon OrMon
natToBool = record { morphs = morph
                   ; preserv = pres
                   }
          where morph : (s : sorts monSig) → Carrier (isorts PlusMon s) → Carrier (isorts OrMon s)
                morph S 0 = false
                morph S (suc _) = true

                pres : (f : funcs monSig) → homPreserv monSig PlusMon OrMon morph f
                pres unit = lift _≡_.refl
                pres mult (zero , zero) = _≡_.refl
                pres mult (zero , suc m) = _≡_.refl
                pres mult (suc n , m) = _≡_.refl

-- 4. isApp

listToBool : Homomorphism monSig ListMon OrMon
listToBool = record { morphs = morph
                    ; preserv = pres
                    }
           where morph : (s : sorts monSig) → Carrier (isorts ListMon s) → Carrier (isorts OrMon s)
                 morph S [] = false
                 morph S (_ ∷ _) = true

                 pres : (f : funcs monSig) → homPreserv monSig ListMon OrMon morph f
                 pres unit = lift _≡_.refl
                 pres mult ([] , []) = _≡_.refl
                 pres mult ([] , _ ∷ _) = _≡_.refl
                 pres mult (_ ∷ _ , _) = _≡_.refl
                      
  
-- Ahora podemos probar: listToBool =  natToBool · listToNat
-- este sería un buen ejemplo para testear la definición de igualdad de homos.
