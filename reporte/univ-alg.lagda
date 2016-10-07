%if False
\begin{code}
module reporte.univ-alg where
\end{code}
%endif
\section{Universal Algebra}
\label{sec:univ-alg}

% Quizás podemos dejar la comparación para la conclusión.
In this section we present our formalization in Agda of the core
concepts of heterogenouos universal algebra, up to initiality of the
term algebra. As far as we know, there are two formalizations of
(multisorted) universal algebra: Capretta's implementation in Coq and
\citet{kahl-2011} monumental formalization of allegories. In this
work, we depart from Capretta at some points, both because of some
theoretical considerations and also because our practical
interest in using universal algebra for constructing a correct
compiler.

% \paragraph{Agda}
% Agda is a functional programming language with dependent types, based on the
% Martin Löf's intuitionistic type theory...

We will motivate some of the main definitions of the development and
show its more interesting parts, while ommiting some technical
details. The full code is available at
\url{https://cs.famaf.unc.edu.ar/~mpagano/univ-alg/}.

\subsection{Signature, algebra and homomorphism}

We recall some basic definitions of multisorted universal algebra
following the \textit{Handbook of Logic in Computer Science},
\cite{handbook}.

\paragraph{Signature}

%if False
\begin{code}

module reporte where

open import Relation.Binary hiding (_⇒_;Total) public
open import Level renaming (suc to lsuc ; zero to lzero) public
open import Data.Nat renaming (_⊔_ to _⊔ₙ_) public
open import Data.Product renaming (map to pmap) public
open import Function public 
open import Function.Equality using (_⟶_;_⟨$⟩_;Π) renaming (_∘_ to _∘ₛ_)  public
open import Data.List hiding ([_];zip) public
open import Relation.Binary.PropositionalEquality as PE hiding ([_];isEquivalence) public
open import Data.String using (String) public
 
open import VecH public

open Setoid

infixr 2 _➜_

pattern _⇒_ ar s = (ar , s)

Ty : (S : Set) → Set
Ty S = List S × S

_➜_ : {S : Set} → List S → S → Ty S
ls ➜ s = (ls , s)

[_,_] : {S : Set} → S → S → List S
[ a , b ] = a ∷ (b ∷ []) 

Vec : ∀ {l} {I : Set} (A : I -> Set l) → List I → Set l
Vec {l} {I} = VecH {l} I
\end{code}
%endif

A \emph{signature} is a pair of sets $(S,F)$, called \textit{sorts} and \textit{operations} (or \textit{function symbols}) respectively. An operation is a triple $(f,[s_1,\ldots,s_n],s)$ consisting of a \textit{name}, a list of sorts (its \textit{arity)}, and another sort (its \textit{target sort}). We write operations as a type declaration $f : [s_1,...,s_n] \Rightarrow s$ and say ``$f$ has type $[s_1,...,s_n] \Rightarrow s$''. %\footnote{In the bibliography of heterogeneous universal algebras the notion of arity may change. In the handbook is called \textit{arity} to what we call \textit{type}.}

There is one alternative way of specifying the operations, one that
seems to us more type-theoretically, as a family of sets (of
operations) indexed by (their) types. We use a record to represent
signatures in Agda, the field |sorts| is a Set and |ops| is a family
of sets indexed by the types of operations:
\begin{code}
record Signature : Set₁ where
  constructor ⟨_,_⟩
  field
    sorts  : Set
    ops  : List sorts × sorts → Set 

  Arity : Set
  Arity = List sorts
  
  Type : Set
  Type = Arity × sorts
\end{code}

%if False
\begin{code}
  dom : ∀ {ar s} → ops (ar ⇒ s) → Arity
  dom {ar} _ = ar
  
_✳_ : ∀ {l₁ l₂} → {I : Set} → (A : I → Setoid l₁ l₂) →
                                 List I → Setoid _ _
_✳_ {I = I} = VecSet I

∥_∥ : ∀ {l₁ l₂} → (Setoid l₁ l₂) → Set l₁
∥_∥ {l₁} {l₂} S = Carrier S
\end{code}
%endif


\noindent This way of defining the set of operations offers two
advantages. On the one hand, we can have an infinite number of sorts
and also of operations; and, more important, we can naturally
define functions or predicates over operations of a given type. 

An example of a signature with infinite operations, a constant for
each natural number and a constant for each (program) variable,  
is that of arithmetic expressions presented in the introduction. 
Let us set |Var = String| for concreteness.
%if False
\begin{code}
Var : Set
Var = String
\end{code}
%endif
\begin{code}
data Sortsₑ : Set where ExprN : Sortsₑ

data Opsₑ : List Sortsₑ × Sortsₑ → Set where
  valN  : (n : ℕ)   → Opsₑ ([] ➜ ExprN)
  varN  : (v : Var) → Opsₑ ([] ➜ ExprN)
  plus  : Opsₑ ([ ExprN , ExprN ] ➜ ExprN )

Σₑ : Signature
Σₑ = ⟨ Sortsₑ , Opsₑ ⟩
\end{code}

\paragraph{Algebra}
Usually, an \emph{algebra} $\mathcal{A}$ of a signature $\Sigma$, or a $\Sigma$-algebra, consists
of a family of sets indexed by the sorts of $\Sigma$ and a family of functions indexed by the operations of $\Sigma$. We use $\mathcal{A}_s$ for the \emph{interpretation} or the \emph{carrier} of the sort $s$; given an operation $f \colon [s_1,...,s_n] \Rightarrow s$, the interpretation of $f$ is a total function $f_{\mathcal{A}}\colon \mathcal{A}_{s_1} \times ... \times \mathcal{A}_{s_n} \rightarrow \mathcal{A}_s$. 

In type-theory, however types are not enough. The commutativity of the
diagram expressing the correctness of the compiler ammounts to show
that two functions, namely $\mathit{enc}\, \mathbin{\circ}\,
\mathit{hsem}$ and $\widehat{\mathit{hexec}}\, \mathbin{\circ}\,
\mathit{comp}$, applied to the same expression are equal. But the
result are functions and it is likely to happen that they are
extensional equal, but not convertible. The well-known solution (for a
detailed discussion see \citet{barthe-setoids-2003}) is to let the
carriers be setoids, \ie a type equipped with an equivalence
relation. In this way we can set the carrier $\widehat{\mathit{Exec}}$
be the appropiate set of functions whose equivalence relation is
extensional equality.

%TODO: ver si decimos algo más de setoides; quizás citar el paper
% de Thorsten Altenkirch.

% \paragraph{Setoids} blabla

% Let's define the interpretation of sorts (or carriers):

%TODO: encajar esto mejor.
As far as possible, we use the standard library
\citep{danielsson-agdalib} definitions; for instance, setoids are
defined as a record with fields: the |Carrier : Set|, the
relation |_≈_ : Rel Carrier|, and the proof that |IsEquivalence _≈_|.

Once sorts are interpreted as setoids, operations should be
interpreted as setoid morphisms; \ie. functions which preserve the
equivalence relation.  Given two setoids |(A,_≈A_,_)| and |(B,_≈B_,_)|,
the type |A ⟶ B| corresponds to the type of functions |f : A → B| that
come with a proof of the preservation,
|cong : ∀ a a' → a ≈A a' → f a ≈B f a'|. 

We formalize the product $\mathcal{A}_{s_1} \times ... \times
\mathcal{A}_{s_n}$ as the setoid of \emph{heterogeneous vectors}. The
type of heterogeneous vectors is parameterized by a set of codes
(sorts) and a family of sets indexed by those codes and indexed over a
list of codes:
\begin{code}
data VecH' {I} (A : I -> Set) : List I → Set where
  ⟨⟩   : VecH' {I} A []
  _▹_  :  ∀ {i is} → A i →
            VecH' A is → VecH' A (i ∷ is)
\end{code}
When |A| is a family of setoids |I → Setoid| it is straightforward to
promote this construction to setoids and we use |A ✳ is| to refer to
the setoid of heterogeneous vectors where the equivalence relation is
the point-wisely induced. The interpretation of the operation $f
\colon [s_1,…,s_n] \Rightarrow s$ should be a setoid morphism |A ✳
[s₁,…,sₙ] ⟶ A s|.

An algebra for a signature $\Sigma$ is a record with two fields: the
interpretation for sorts and the interpretation for operations.
%if False
\begin{code}
open Signature
\end{code}
%endif
\begin{code}
record Algebra {ℓ₁ ℓ₂}  (Σ : Signature) :
                                Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  constructor 〈_,_〉
  field
    _⟦_⟧ₛ   : sorts Σ → Setoid ℓ₁ ℓ₂
    _⟦_⟧ₒ    : ∀ {ar s} → ops Σ (ar ➜ s) →
                _⟦_⟧ₛ ✳ ar ⟶ _⟦_⟧ₛ s
\end{code}
%if False
\begin{code}
  _⟦_⟧ₛ* : (ar : Arity Σ) → Setoid _ _
  _⟦_⟧ₛ*  ar = _⟦_⟧ₛ ✳ ar
\end{code}
%endif

% TODO: sacar esto y poner algo más conciso?

%We define too a type representing the domain of an interpretation of function symbol,
%wich will be useful in later definitions.
%If |ar| is the arity of an operation |f|, the interpretation will be a function between
%setoids, with domain the heterogeneous vectors with arity |ar| and interpretation |_⟦_⟧ₛ A|:
%
%\begin{spec}
%_⟦_⟧ₛ* : ∀ {Σ} {ℓ₁} {ℓ₂}  → (A : Algebra {ℓ₁} {ℓ₂} Σ)
%                          → (ar : Arity Σ) → Set _
%_⟦_⟧ₛ* {Σ} A ar = Carrier (VecSetoid (sorts Σ) (_⟦_⟧ₛ A) ar)
%\end{spec}
%
%\medskip
Let see an example of a |Σₑ|-algebra, the semantics of the expression
language that we introduced previously. We let |State = Var → ℕ| and
intepret the only sort |ExprN| as the setoid whose carrier are
functions in |State → ℕ| with |f ≈ g| if for every state |σ|, 
|f σ ≡ g σ|; this last equality is the definitional equality of Agda.
%if False
\begin{code}
State : Set
State = Var → ℕ
open Signature
pattern ⟨⟨_,_⟩⟩ a b = a ▹ (b ▹ ⟨⟩) 
\end{code}
%endif
The function |→-setoid| from the standard library builds
the setoid we just described.
%if False
\begin{code}
private 
\end{code}
%endif
\begin{code}
  ⟦_⟧ : sorts Σₑ → Setoid _ _
  ⟦ _ ⟧ = State →-setoid ℕ
\end{code}
The interpretation of operations is piecewise-defined according to
their types. Remember that besides the function, one must provide the
proof of preservation of equalities; we omit these proofs as they
are utterly uninteresting.
\begin{spec}
i : ∀ {ar s} → ops Σₑ (ar ➜ s) → ⟦_⟧ ✳ ar ⟶ ⟦ s ⟧
i (valN n) = record  { _⟨$⟩_ = λ {⟨⟩ σ → n }
                     ; cong = {!!} }
i (varN v) = record  { _⟨$⟩_ = λ {⟨⟩ σ → σ v }
                     ; cong = {!!} }
i plus = record  { _⟨$⟩_ = λ {⟨⟨ f , g ⟩⟩  σ → f σ + g σ}
                 ; cong = {!!}}
\end{spec}
%if False
\begin{code}
  iₒ : ∀ {ar s} → (f : ops Σₑ (ar ⇒ s)) → ∥ ⟦_⟧ ✳ ar ∥ → ∥ ⟦ s ⟧ ∥
  iₒ (valN n) ⟨⟩ = λ σ → n
  iₒ (plus) (v₀ ▹ (v₁ ▹ ⟨⟩)) = λ σ → v₀ σ + v₁ σ
  iₒ (varN x) ⟨⟩ = λ σ → σ x

  iₚ : ∀ {ar} {s} → (f : ops Σₑ (ar ⇒ s)) →
           {vs vs' : ∥ ⟦_⟧ ✳ ar ∥ } →
           _∼v_ {R = _≈_ ∘ ⟦_⟧} vs vs' →
           _≈_ (⟦  s ⟧) (iₒ f vs) (iₒ f vs')
  iₚ (valN n) {⟨⟩} ∼⟨⟩ = λ σ → _≡_.refl
  iₚ plus {v₀ ▹ (v₀' ▹ ⟨⟩)} {v₁ ▹ (v₁' ▹ ⟨⟩)} (∼▹ v₀≈v₁ (∼▹ v₀'≈v₁' ∼⟨⟩)) =
                           λ σ → cong₂ _+_ (v₀≈v₁ σ) (v₀'≈v₁' σ)
  iₚ (varN v) {⟨⟩} ∼⟨⟩ = λ σ → _≡_.refl

  i : ∀ {ar s} → ops Σₑ (ar ➜ s) → ⟦_⟧ ✳ ar ⟶ ⟦ s ⟧
  i f = record  { _⟨$⟩_ = iₒ f ; cong = iₚ f }
\end{code}
%endif
Notice that Agda infers that there are no arguments for nullary
operators; since |plus| has arity |[ExprN,ExprN]| and we can
pattern-matching on |⟦_⟧ ✳ [ExprN,ExprN]| and define the
interpretation as we did in the introduction. We have thus
defined the algebra $\mathit{Sem}$:
\begin{code}
Semₑ : Algebra Σₑ
Semₑ = 〈 ⟦_⟧ , i 〉
\end{code}
%if False
\begin{code}
open Algebra
\end{code}
%endif

\paragraph{Homomorphism}

Let $\mathcal{A}$ and $\mathcal{B}$ be two $\Sigma$-algebras, a \emph{homomorphism}
$h$ from $\mathcal{A}$ to $\mathcal{B}$ is a family of functions indexed by the
sorts $h_s : \mathcal{A}_s \rightarrow \mathcal{B}_s$,
such that for each operation $f : [s_1,...,s_n] \Rightarrow s$, the following holds:
\begin{equation}
  h_s(f_{\mathcal{A}}(a_1,...,a_n)) = f_{\mathcal{B}}(h_{s_1}\,a_1,...,h_{s_n}\,a_n)\label{eq:homcond}
\end{equation}

We formalize an homomorphism as a record with the family of functions
and a proof that it satisfies condition \eqref{eq:homcond}. In order to
avoid repetition of the same parameters over and over again, we declare
a module parameterized over the signature and the algebras.
\begin{code}
module Hom {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Σ}
        (A : Algebra {ℓ₁} {ℓ₂} Σ) 
        (B : Algebra {ℓ₃} {ℓ₄} Σ) where 
\end{code}
\begin{code}
  _⟿_ : Set _
  _⟿_ = (s : sorts Σ) → (A ⟦ s ⟧ₛ) ⟶ (B ⟦ s ⟧ₛ)
\end{code}
An element |h : A ⟿ B| will be a family of setoid morphisms between
the interpretation of each sort in the source and target algebras.  In
order to encode condition \eqref{eq:homcond} we need to map |h| over
the heterogeneous vector |as : A ⟦ ar ⟧ₛ*|. We let |map⟿ h ts = mapV
(_⟨$⟩_ ∘ h) ts|, where |mapV| is mapping over heterogeneous vectors.
%if False
\begin{code}
  map⟿ : ∀ {ar} → (h : _⟿_) →  ∥ A ⟦ ar ⟧ₛ* ∥ → ∥ B ⟦ ar ⟧ₛ* ∥
  map⟿ h ts = mapV (_⟨$⟩_ ∘ h) ts
\end{code}
%endif
\noindent Now we can state condition \eqref{eq:homcond} replacing
equality by the corresponding equivalence relation, so let |_≈ₛ_ = _≈_ (B ⟦ s ⟧ₛ)|:
\begin{code}
  homCond : ∀ ty → _⟿_ → ops Σ ty → Set _
  homCond (ar ⇒ s) h f = (as : ∥ A ⟦ ar ⟧ₛ* ∥) →
       h s ⟨$⟩ (A ⟦ f ⟧ₒ ⟨$⟩ as) ≈ₛ B ⟦ f ⟧ₒ ⟨$⟩ map⟿ h as
\end{code}
%if False
\begin{code}
         where  _≈ₛ_ : _
                _≈ₛ_ = _≈_ (B ⟦ s ⟧ₛ)
                infixr 0 _≈ₛ_ 
\end{code}
%endif

\noindent For |H : Homo A B|, the setoid morphism is |′ H ′ : A ⟿ B| and
|cond H| is the proof that |′ H ′| satisfies \eqref{eq:homcond}.
%if False
\begin{code}
  ℓ' : _
  ℓ' = lsuc (ℓ₄ ⊔ ℓ₃ ⊔ ℓ₁ ⊔ ℓ₂)
\end{code}
%endif
\begin{code}
  record Homo : Set ℓ' where
    field
      ′_′  : _⟿_
      cond : ∀ {ty} (f : ops Σ ty) → homCond ty ′_′ f
\end{code}


\subsection{The Term Algebra is Initial}

A $\Sigma$-algebra $\mathcal{A}$ is called \emph{initial} if for all
$\Sigma$-algebra $\mathcal{B}$ there exists exactly one homomorphism
from $\mathcal{A}$ to $\mathcal{B}$. This universal condition should be
stated with respect to some underlying notion of equality.

Informally, if $≈$ is an equivalence relation over $A$,
we can say that an element $a \in A$ is unique if $A = [a]_{≈}$;
from which we can easily deduce that uniqueness is contagious: if someone
is unique, everyone is! Less picturesque we define uniqueness through
totality:
\begin{code}
Total : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → Rel A ℓ₂ → Set _ 
Total _≈_ = ∀ a a' → a ≈ a'
\end{code}
%if False
\begin{code}
data False : Set where

TotalEmpty : ∀ {ℓ₁} → (r : Rel False ℓ₁) → Total r
TotalEmpty _≈_ () _
\end{code}
%endif
Since we cannot extract a witness from a proof that a relation
is total (notice that every relation over the empty type is total),
we ask for a concrete witness of uniqueness:
\begin{code}
Unique : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → Rel A ℓ₂ → Set _
Unique {A = A} _≈_ = A × Total _≈_ 
\end{code}
%if False
\begin{code}
UniqueContagious : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → (_≈_ : Rel A ℓ₂) →
  (a : A) → Unique _≈_ → ∃ {A = Unique {A = A} _≈_} (λ p → (proj₁ p) ≡ a)
UniqueContagious _≈_ a prf = (a , proj₂ prf) , _≡_.refl
\end{code}
%endif

As we have explained to justify the use of setoids, the appropiate
notion of equality between homomorphisms is extensional equality.  We
define a type to represent the property of extensional equality. If
|A,≈A| and |B,≈B| are setoids and |f g : A ⟶ B| are setoid morphisms,
we say that they are extensionally equal if they are equal point-wise.
%if False
\begin{code}
module ExtEq {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Setoid ℓ₁ ℓ₂} {B : Setoid ℓ₃ ℓ₄} where
  private
    _≈B_ : _
    _≈B_ = _≈_ B

    _≈A_ : _
    _≈A_ = _≈_ A

\end{code}
%endif
\begin{code}
  _≈→_ : Rel (A ⟶ B) _
  f ≈→ g  = ∀ (a : Carrier A) → (f ⟨$⟩ a) ≈B (g ⟨$⟩ a)
\end{code}
We can deduce that |a ≈A a'| implies |f a ≈B g a'| by a simple equational
reasoning. Moreover, we can prove that |_≈→_| is an equivalence relation.
\begin{spec}
  Equiv≈→ : IsEquivalence (_≈→_)
  Equiv≈→ = {!!}
\end{spec}
%if False
\begin{code}
  ≈→-preserves-≈ : ∀ a a' f g → f ≈→ g → a ≈A a' → (f ⟨$⟩ a) ≈B (g ⟨$⟩ a')
  ≈→-preserves-≈ a a' f g f≈g a≈a' = begin⟨ B ⟩
                                     f ⟨$⟩ a
                                     ≈⟨ Π.cong f a≈a' ⟩
                                     f ⟨$⟩ a'
                                     ≈⟨ f≈g a' ⟩
                                     g ⟨$⟩ a'
                                     ∎
    where open import Relation.Binary.SetoidReasoning 
    
  Equiv≈→ : IsEquivalence (_≈→_)
  Equiv≈→ = record { refl = λ {f} → isRefl {f}
                                    ; sym = λ {f} {g} prf → isSym {f} {g} prf
                                    ; trans = λ {f} {g} {h} p q → isTrans {f} {g} {h} p q }
    where isRefl : Reflexive (_≈→_)
          isRefl {f} a = Setoid.refl B {f ⟨$⟩ a}
          isSym : Symmetric (_≈→_)
          isSym {f} {g} p a = Setoid.sym B (p a)
          isTrans : Transitive (_≈→_)
          isTrans {f} {g} {h} p q a = Setoid.trans B (p a) (q a)
\end{code}
%endif
Two homomorphisms |H G : Homo A B| are equals if for every sort |s|,
its corresponding setoid morphisms are extensional equal, that is
|′ H ′ s ≈→ ′ G ′ s|.
%if False
\begin{code}
module EqHomo {ℓ₁ ℓ₂ ℓ₃ ℓ₄} Σ {A : Algebra {ℓ₁} {ℓ₂} Σ} {B : Algebra {ℓ₃} {ℓ₄} Σ} where
  open Hom
  open Homo
  open Algebra
  open ExtEq
  open IsEquivalence renaming (refl to ref;sym to symm;trans to tran)
\end{code}
%endif
\begin{code}
  _≈ₕ_  : (H G : Homo A B) → Set _
  H ≈ₕ G = (s : sorts Σ) → ′ H ′ s ≈→ ′ G ′ s
\end{code}

The relation |_≈ₕ_| is an equivalence relation, which easily follows from
|_≈→_| being an equivalence.
\begin{spec}
  equiv≈ₕ : IsEquivalence _≈ₕ_
  equiv≈ₕ = {!!}
\end{spec}
%if False
\begin{code}
  ≈A→B : (s : sorts Σ) → IsEquivalence (_≈→_ {A = A ⟦ s ⟧ₛ} {B = B ⟦ s ⟧ₛ})
  ≈A→B s = Equiv≈→ {A = A ⟦ s ⟧ₛ} {B = B ⟦ s ⟧ₛ}
  equiv≈ₕ : IsEquivalence _≈ₕ_
  equiv≈ₕ = record { refl = λ {h} s a → ref (≈A→B s)  {′ h ′ s} a
                   ; sym = λ {h} {g} eq s a → symm (≈A→B s) {′ h ′ s} {′ g ′ s} (eq s) a
                   ; trans = λ {f} {g} {h} eq eq' s a →
                           tran (≈A→B s) {′ f ′ s} {′ g ′ s} {′ h ′ s} (eq s) (eq' s) a }
\end{code}
%endif

In order to construct an initial algebra (we could say ``the initial
algebra'' up to isomorphism), we have to provide the algebra, say
$\mathcal{I}$ and a proof of uniqueness for the homomorphism from
$\mathcal{I}$ to any other algebra $\mathcal{A}$. Thus, in the formalization
this notion is captured by the following record:
%if False
\begin{code}
module Initial {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} (Σ : Signature) where
  open Hom
  open EqHomo
\end{code}
%endif
\begin{code}
  record Initial  : Set (lsuc (ℓ₄ ⊔ ℓ₃ ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      alg   : Algebra {ℓ₁} {ℓ₂} Σ
      init  : (A : Algebra {ℓ₃} {ℓ₄} Σ) →
                  Unique (_≈ₕ_ Σ {alg} {A})
\end{code}


\paragraph{Term algebra}

Given a signature $\Sigma$ we can define the \emph{term algebra}
$\mathcal{T}$, whose carriers are sets of well-typed words built up
from the function symbols.  Sometimes this universe is called the
\emph{Herbrand Universe} (although, according to \cite{wirth-2009},
Herbrand did not thought of $\mathcal{T}$ but only finite
approximations of it). It is customary to use an inductive definition
for $\mathcal{T}$:
\[
\inferrule*{f : [s_0,...,s_{n-1}] \Rightarrow s\\  \text{ for all } 0 \leq i \leq n-1,\  t_i \in \mathcal{T}_{s_i} }
{f\,(t_0,...,t_{n-1}) \in \mathcal{T}_s}
\]
This inductive definition can be directly written in Agda:
%if False
\begin{code}
module TermAlgebra (Σ : Signature) where
\end{code}
%endif
\begin{code}
  data HU : (s : sorts Σ) → Set where
    term : ∀  {ar s} →  (f : ops Σ (ar ⇒ s)) →
               (Vec HU ar) → HU s
\end{code}

%% MIGUEL: no creo que sean necesarios estos ejemplos.
% \paragraph{Example}
% Let's define some terms of the signature |Σₑ|:

% \begin{spec}
% t₁ : HU Σₑ E
% t₁ = term (valN 2) ⟨⟩

% t₂ : HU Σₑ E
% t₂ = term (varN " x ") ⟨⟩

% t₃ : HU Σₑ E
% t₃ = term plus (t₁ ▹ t₂ ▹ ⟨⟩)
% \end{spec}

\noindent We use propositional equality to turn each $\mathcal{T}_s$ in a
setoid, thus completing the interpretation of sorts. To interpret
an operation $f \colon [s_1,\ldots,s_n] \Rightarrow s$ we map the
tuple $⟨t_1,\ldots,t_n⟩$ to $f(t_1,\ldots,t_n)$; we omit the proof
of |cong|.
\begin{spec}
  |T| : Algebra Σ
  |T| = 〈setoid ∘ HU ,
           λ f → record  { _⟨$⟩_ = term f ; cong = {!!}} 〉
\end{spec}
%if False
\begin{code}
  |T| : Algebra Σ
  |T| = record  { _⟦_⟧ₛ = setoid ∘ HU
                ; _⟦_⟧ₒ  = ∣_|ₒ
                }
    where ≡vec : ∀ {ar}  → (ts₁ ts₂ : VecH _ HU ar) →
                   _∼v_ {R = λ _ → _≡_} ts₁ ts₂ →
                   ts₁ ≡ ts₂
          ≡vec ⟨⟩ ⟨⟩ ≈⟨⟩ = PE.refl
          ≡vec (t ▹ ts₁) (.t ▹ ts₂) (∼▹ PE.refl ts₁≈ts₂) =
                                    PE.cong (λ ts → t ▹ ts) (≡vec ts₁ ts₂ ts₁≈ts₂)
          fcong : ∀ {ar s} {f : ops Σ (ar ⇒ s)} →
                              (ts₁ ts₂ : VecH _ HU ar) →
                             _∼v_ {R = λ s₀ → _≡_} ts₁ ts₂ →
                             term f ts₁ ≡ term f ts₂
          fcong {f = f} ts₁ ts₂ ts₁≈ts₂ = PE.cong (term f) (≡vec ts₁ ts₂ ts₁≈ts₂)
          ∣_|ₒ  : ∀ {ar s} → ops Σ (ar ⇒ s) → (setoid ∘ HU) ✳ ar ⟶ (setoid ∘ HU) s
          ∣ f |ₒ = record { _⟨$⟩_ = term f
                          ; cong = λ {ts₁} {ts₂} ts₁≈ts₂ → fcong ts₁ ts₂ ts₁≈ts₂
                          }
                          
\end{code}
%endif
\noindent Now we turn to prove that the term algebra is initial; so for any
$\Sigma$-algebra $\mathcal{A}$ we define the homomorphism $h_A \colon
\mathcal{T} \to \mathcal{A}$ \[
  h_A (f(t_1,\ldots,t_n)) = f_{\mathcal{A}}\,(h_A\,t_1,...,h_A\,t_n) \enspace .
\] 
\noindent One would like to define this map in Agda just like that:
\begin{spec}
  ∣h∣→A : ∀ {s : sorts Σ} → HU s → ∥ A ⟦ s ⟧ₛ ∥
  ∣h∣→A (term f ts) = A ⟦ f ⟧ₒ ⟨$⟩ (mapV ∣h∣→A ts)
\end{spec}

\noindent The termination checker, however, cannot ensure the
termination; so we define two mutually recursive functions, one
mappings terms to elements of $\mathcal{A}$ and the other mapping
vectors of terms to vectors of $\mathcal{A}$, of course respecting
the sorts.
%if False
\begin{code}
module InitHomo {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} {Σ : Signature} (A : Algebra {ℓ₃} {ℓ₄} Σ) where
  open TermAlgebra Σ
  open Hom |T| A
  open Homo
  open EqHomo Σ {|T|} {A}
\end{code}
%endif
\begin{code}
  mutual
    ∣h∣→A : {s : sorts Σ} → HU s → ∥ A ⟦ s ⟧ₛ ∥
    ∣h∣→A (term f ⟨⟩)         =   A ⟦ f ⟧ₒ ⟨$⟩ ⟨⟩
    ∣h∣→A (term f (t ▹ ts))   =   A ⟦ f ⟧ₒ ⟨$⟩ (∣h∣→A t ▹ map|h|→A ts)

    map|h|→A : ∀ {ar} → ∥ |T| ⟦ ar ⟧ₛ* ∥ → ∥ A ⟦ ar ⟧ₛ* ∥
    map|h|→A ⟨⟩ = ⟨⟩
    map|h|→A (t ▹ ts) = ∣h∣→A t ▹ map|h|→A ts
\end{code}
It is trivial to show that |∣h∣→A| respects the (trivial) equality on
terms and also satisfies the homomorphism condition.
\begin{spec}
  |h|A : Homo
  |h|A = record  { ′_′  = λ s → record 
                   {_⟨$⟩_ = ∣h∣→A {s} ; cong  = {!!}}
                 ; cond = {!!}}
\end{spec}
%if False
\begin{code}
  map|T|→A≡mapV : ∀ {ar} {ts : ∥ |T| ⟦ ar ⟧ₛ*  ∥} →
                map|h|→A ts ≡ mapV (λ s → ∣h∣→A {s}) ts
  map|T|→A≡mapV {ar = []} {⟨⟩} = PE.refl
  map|T|→A≡mapV {s ∷ ar} {t ▹ ts} =
                 PE.cong (λ ts' → ∣h∣→A t ▹ ts') map|T|→A≡mapV
      
  ≡to≈ : ∀ {ℓ₁} {ℓ₂} {St : Setoid ℓ₁ ℓ₂} {x y : Carrier St} →
     x ≡ y → _≈_ St x y
  ≡to≈ {St = St} PE.refl = Setoid.refl St

  congfun : ∀ {s} {t₁ t₂ : HU s} →
                  t₁ ≡ t₂ → _≈_ (A ⟦ s ⟧ₛ) (∣h∣→A t₁) (∣h∣→A t₂)
  congfun {s} t₁≡t₂ = ≡to≈ {St = A ⟦ s ⟧ₛ} (PE.cong ∣h∣→A t₁≡t₂)
  fun|T|ₕ : |T| Hom.⟿ A
  fun|T|ₕ s = record { _⟨$⟩_ = ∣h∣→A {s} ; cong  = congfun}
  |T|ₕcond : ∀ {ty} (f : ops Σ ty) → homCond ty fun|T|ₕ f
  |T|ₕcond {_ ⇒ s} f ⟨⟩ = ≡to≈ {St = A ⟦ s ⟧ₛ} PE.refl
  |T|ₕcond {_ ⇒ s} f (t ▹ ts) =
           ≡to≈ {St = A ⟦ s ⟧ₛ}
                (PE.cong (λ ts' → A ⟦ f ⟧ₒ ⟨$⟩ (∣h∣→A t ▹ ts'))
                         map|T|→A≡mapV)


  |h|A : Homo
  |h|A = record { ′_′  = fun|T|ₕ
                 ; cond = |T|ₕcond }
  import Relation.Binary.EqReasoning as EqR
\end{code}
%endif

The proof of initiality is finished once we prove that any pair of
homomorphisms $H,G \colon \mathcal{T} \to \mathcal{A}$ are equal; \ie
$H\,f(t_0,\ldots,t_{n-1}) ≈ f(t_0,\ldots,t_{n-1})$, for any term
$f(t_0,\ldots,t_{n-1})$.
\begin{code}
  total : Total _≈ₕ_
  total H G s (term {ar = ar} f ts) = 
            begin
              ′ H ′ s ⟨$⟩ term f ts
                ≈⟨ cond H f ts ⟩
              A ⟦ f ⟧ₒ ⟨$⟩ (map⟿ ′ H ′ ts)
                ≈⟨ Π.cong (A ⟦ f ⟧ₒ) (map≈ ar ts) ⟩
              A ⟦ f ⟧ₒ ⟨$⟩ (map⟿ ′ G ′ ts)
                ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (cond G f ts) ⟩ 
              ′ G ′ s ⟨$⟩ term f ts
            ∎
\end{code}
\noindent In that proof we used the facilities for equational
reasoning provided by the standard library. We omit the proof
|map≈| showing |map H ts ≈ map G ts|.
%if False
\begin{code}
    where open EqR (A ⟦ s ⟧ₛ)
          map≈ : (ar : Arity Σ) → (ts : VecH (sorts Σ) (HU) ar) →
                  (mapV (_⟨$⟩_ ∘ ′ H ′) ts) ∼v
                  (mapV (_⟨$⟩_ ∘ ′ G ′) ts)
          map≈ [] ⟨⟩ = ∼⟨⟩
          map≈ (s ∷ ar) (t ▹ ts) = ∼▹ (total H G s t)
                                      (map≈ ar ts)

  tinit : Unique _≈ₕ_
  tinit = |h|A , total
\end{code}
%endif
