{-# OPTIONS --allow-unsolved-metas #-}
module Charla.Tipos where

{- Las reglas de introducción son los _constructores_ del tipo. -}
{- Una prueba de una proposición se puede probar si podemos construir
un término de ese tipo. -}

data _∧_ : (P Q : Set) → Set where
  conjI : ∀ {P Q} →
          (p : P) → (q : Q) →
          -------------------
          P ∧ Q

data _∨_ : (P Q : Set) → Set where
  disjI₁ : ∀ {P Q} → (p : P) → P ∨ Q
  disjI₂ : ∀ {P Q} → (q : Q) → P ∨ Q

data ⊤ : Set where
  trivial : ⊤

data ⊥ : Set where
-- notar que no hay constructor

{- Las reglas de eliminación las podemos definir analizando las
  posibles formas (normales) de cada prueba. -}

conjE₁ : {P Q : Set} → P ∧ Q → P
conjE₁ (conjI p q) = p

conjE₂ : {P Q : Set} → P ∧ Q → Q
conjE₂ (conjI p q) = q

conjE' : {P Q : Set} → P ∧ (P ∧ Q) → P
conjE' (conjI p q) = conjE₁ q

disjE : {P Q R : Set} → (P → R) → (Q → R) → P ∨ Q → R
disjE f g (disjI₁ p) = f p
disjE f g (disjI₂ q) = g q

{- El análisis por caso puede ser más profundo y Agda nos asiste. -}
distr : {P Q R : Set} →
        P ∨ (Q ∧ R) →
        (P ∨ Q) ∧ (P ∨ R)
distr {P} {Q} {R} (disjI₁ p) = conjI (disjI₁ p) (disjI₁ p)
distr (disjI₂ (conjI q r)) = conjI (disjI₂ q) (disjI₂ r)


elim-⊥ : {P : Set} → (prf : ⊥) → P
elim-⊥ ()


{- La cuantificación universal se codifica con el espacio de funciones
dependientes. -}

data Forall : (A : Set) → (P : A → Set) → Set where
  all : ∀ {A P} → ((a : A) → P a) → Forall A P

{- y los existenciales como un par de un testigo y la prueba que satisface
el predicado -}

data Exists : (A : Set) → (P : A → Set) → Set where
  ex : ∀ {A P} → (a : A) → P a → Exists A P


-- Los conjuntos los definimos inductivamente (también se pueden
-- definir coinductivamente pero no nos interesa)
data Bool : Set where
  true false : Bool

and : Bool → Bool → Bool
and true b' = b'
and false b' = false

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

_+_ : Nat → Nat → Nat
zero + m = m
suc n + m = suc (n + m)

-- Un predicado como ya vimos es un tipo indexado en otro
data Even : Nat → Set where
  zeroEven : Even zero
  2+Even   : ∀ {n} → Even n → Even (suc (suc n))

nat→nat : Set
nat→nat = Nat → Nat

data ¬_ : (P : Set) → Set where
  negI : ∀ {P} → (P → ⊥) → ¬ P

-- cantor : (h : Nat → (Nat → Nat)) →
--        ((f : Nat → Nat) → Σ[ n ∈ Nat ] (∀ i → f i ≡ h n i)) → ⊥
-- cantor = ?        

-- ¬ (Even (suc zero))
oneIsEven : Even (suc zero) → ⊥
oneIsEven ()

twoIsEven : Even (suc (suc zero))
twoIsEven = 2+Even zeroEven

-- La igualdad es una relación
data _≡_ : {A : Set} (x y : A) → Set where
  refl : ∀ {A} {a : A} → a ≡ a

trans : ∀ {A} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

cong : {A B : Set} → {a b : A} → (f : A → B) →
       a ≡ b → f a ≡ f b
cong f refl = refl

0-id-right : ∀ n → (n + zero) ≡ n
0-id-right zero = refl
0-id-right (suc n) = cong suc (0-id-right n)

suc-right : ∀ n m → (n + suc m) ≡ suc (n + m)
suc-right zero m = refl
suc-right (suc n) m = cong suc (suc-right n m)


+-comm : ∀ m n → (m + n) ≡ (n + m)
+-comm m zero = 0-id-right m
+-comm m (suc n) = trans (suc-right m n)
                         (cong suc (+-comm m n))
