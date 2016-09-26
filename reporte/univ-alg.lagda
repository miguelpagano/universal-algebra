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

\subsection*{Signature}

%if False
\begin{code}

module reporte where

open import Relation.Binary
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Nat renaming (_⊔_ to _⊔ₙ_)
open import Data.Product renaming (map to pmap)
open import Function
open import Function.Equality renaming (_∘_ to _∘ₛ_)
open import Data.Bool
open import Data.List hiding ([_])
open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open import Data.String
open import Data.Fin hiding (_+_)
 
open import VecH

open Setoid

infixr 2 _➜_

Ty : (S : Set) → Set
Ty S = List S × S

_➜_ : {S : Set} → List S → S → Ty S
ls ➜ s = (ls , s)

[_,_] : {S : Set} → S → S → List S
[ a , b ] = a ∷ (b ∷ []) 
\end{code}
%endif

A \emph{signature} is a pair of sets $(S,F)$, called \textit{sorts} and \textit{operations} (or \textit{function symbols}) respectively. An operation is a triple $(f,[s_1,\ldots,s_n],s)$ consisting of a \textit{name}, a list of sorts (its \textit{arity)}, and another sort (its \textit{target sort}). We write operations as a type declaration $f : [s_1,...,s_n] \Rightarrow s$ and say ``$f$ has type $[s_1,...,s_n] \Rightarrow s$''. %\footnote{In the bibliography of heterogeneous universal algebras the notion of arity may change. In the handbook is called \textit{arity} to what we call \textit{type}.}

There is one alternative way of specifying the operations, one that
seems to us more type-theoretically, as a family of sets (of
operations) indexed by (their) types. We use a record to represent
signatures in Agda, the field |sorts| is a Set and |funcs| is a family
of sets indexed by the types of operations:
\begin{code}
record Signature : Set₁ where
  constructor ⟨_,_⟩
  field
    sorts  : Set
    funcs  : List sorts × sorts → Set 

  Arity : Set
  Arity = List sorts
  
  Type : Set
  Type = Arity × sorts
\end{code}

%if False
\begin{code}
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
data Sortsₑ : Set where
  ExprN : Sortsₑ

data Funcsₑ : List Sortsₑ × Sortsₑ → Set where
  valN  : (n : ℕ)   → Funcsₑ ([] ➜ ExprN)
  varN  : (v : Var) → Funcsₑ ([] ➜ ExprN)
  plus  : Funcsₑ ([ ExprN , ExprN ] ➜ ExprN )

Σₑ : Signature
Σₑ = ⟨ Sortsₑ , Funcsₑ ⟩
open Signature
\end{code}

\subsection*{Algebra}


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
equivalence relation.  Given two setoids |(A,_≈_,_)| and |(B,_≈'_,_)|,
the type |A ⟶ B| corresponds to the type of functions |f : A → B| that
come with a proof of the preservation, \ie 
|prf : (a a' : A) → a ≈ a' → f a ≈' f a'|. 

We formalize the product $\mathcal{A}_{s_1} \times ... \times
\mathcal{A}_{s_n}$ as the setoid of \emph{heterogeneous vectors}. The
type of heterogeneous vectors is parameterized by a set of codes
(sorts) and a family of sets indexed by those codes and indexed over a
list of codes:
\begin{code}
data HVec {I} (A : I -> Set) : List I → Set where
  ⟨⟩   : HVec {I} A []
  _▹_  :  ∀ {i is} → (v : A i) →
          (vs : HVec A is) → HVec A (i ∷ is)
\end{code}
When |A| is a family of setoids |I → Setoid| it is straightforward to
promote this construction to setoids and we use |A ✳ is| to refer to
the setoid of heterogeneous vectors where the equivalence relation is
the point-wisely induced. The interpretation of the operation $f
\colon [s_1,…,s_n] \Rightarrow s$ should be a setoid morphism |A ✳
[s₁,…,sₙ] ⟶ A s|.

An algebra for a signature $\Sigma$ is a record with two fields: the
interpretation for sorts and the interpretation for operations.
\begin{code}
record Algebra {ℓ₁ ℓ₂}  (Σ : Signature) :
                                Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  constructor ⟪_,_⟫
  field
    _⟦_⟧ₛ   : sorts Σ → Setoid ℓ₁ ℓ₂
    _⟦_⟧    : ∀ {ar s} → (f : funcs Σ (ar , s)) →
                _⟦_⟧ₛ ✳ ar ⟶ _⟦_⟧ₛ s
\end{code}
%if False
\begin{code}
  _⟦_⟧ₛ* : (ar : Arity Σ) → Set _
  _⟦_⟧ₛ*  ar = Carrier ( _⟦_⟧ₛ ✳ ar)
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
We use the function |→-setoid| from the standard library that builds
the setoid we just described.
\begin{code}
⟦_⟧ : sorts Σₑ → Setoid _ _
⟦ _ ⟧ = State →-setoid ℕ
\end{code}
The interpretation of operations is piecewise-defined according to
their types. Remember that besides the function, one must provide the
proof of preservation of equalities; we omit these proofs as they
are utterly uninteresting.
\begin{code}
i : ∀ {ar s} → funcs Σₑ (ar , s) → ⟦_⟧ ✳ ar ⟶ ⟦ s ⟧
i (valN n) = record  { _⟨$⟩_ = λ {⟨⟩ σ → n }
                     ; cong = {!!} }
i (varN v) = record  { _⟨$⟩_ = λ {⟨⟩ σ → σ v }
                     ; cong = {!!} }
i plus = record  { _⟨$⟩_ = λ {⟨⟨ f , g ⟩⟩  σ → f σ + g σ}
                 ; cong = {!!}}
\end{code}
Notice that Agda infers that there are no arguments for nullary
operators; since |plus| has arity |[ExprN,ExprN]| and we can
pattern-matching on |⟦_⟧ ✳ [ExprN,ExprN]| and define the
interpretation as we did in the introduction. We have thus
defined the algebra $\mathit{Sem}$:
\begin{code}
Semₑ : Algebra Σₑ
Semₑ = ⟪ ⟦_⟧ , i ⟫
\end{code}
%if False
\begin{code}
open Algebra
\end{code}
%endif

\subsection*{Homomorphism}

Let $\mathcal{A}$ and $\mathcal{B}$ be two $\Sigma$-algebras, a \textbf{homomorphism}
$h$ from $\mathcal{A}$ to $\mathcal{B}$ is a family of functions indexed by the
sorts $h_s : \mathcal{A}_s \rightarrow \mathcal{B}_s$,
such that for each operation $f : [s_1,...,s_n] \Rightarrow s$, the following holds:
\begin{equation}
  h_s(f_{\mathcal{A}}(a_1,...,a_n)) = f_{\mathcal{B}}(h_{s_1}\,a_1,...,h_{s_n}\,a_n)\label{eq:homcond}
\end{equation}

Let's define first the notion of \textit{function between} $\Sigma$-algebras:

\begin{code}
_⟿_ :  ∀ {ℓ₁ ℓ₂} Σ → (A B : Algebra {ℓ₁} {ℓ₂} Σ) →
         Set _
_⟿_ Σ A B = (s : sorts Σ) → (A ⟦ s ⟧ₛ) ⟶ (B ⟦ s ⟧ₛ)
\end{code}

\noindent Note that for each sort $s$ we have a function between the setoids
corresponding to the interpretation of $s$ in each algebra.

Let's define the condition of homomorphism. In the right side of the equation (1) we have the
application of function $h$ to each element of $(a_1,...,a_n)$. The function |map⟿| allows us to apply a function to a vector.

\begin{spec}
homCond  A A' h f = (as : A ⟦ ar ⟧ₛ*) →  (h s ⟨$⟩ (A ⟦ f ⟧ ⟨$⟩ as))
                                         ≈ₛ 
                                         (A' ⟦ f ⟧ ⟨$⟩ (map⟿ h as))
         where  _≈ₛ_ : _
                _≈ₛ_ = _≈_ (A' ⟦ s ⟧ₛ) 
\end{spec}


%% Procedamos ahora a definir la condición de homomorfismo. En la parte derecha de la ecuación (1) tenemos
%% la aplicación de la función $h$ en cada elemento de $(a_1,...,a_n)$. Definimos esta noción en Agda. Si
%% |ar| es una aridad y |A| una |Σ|-álgebra, definimos como mapear una función entre álgebras |h| a un
%% vector en |A ⟦ ar ⟧ₛ*|. A esta función la notaremos con |map⟿| y no pondremos en este texto
%% su definición.


%% A continuación damos la definición de un tipo para la condición de homomorfismo de
%% una función entre álgebras |h|. Si
%% |h : A ⟿ A'| y |f : funcs Σ (ar , s)|, para todo |(as : A ⟦ ar ⟧ₛ*)|, debe darse
%% la igualdad entre
%% la aplicación de |h| al resultado de aplicar la interpretación de |f| en |A| al vector
%% |as| y la aplicación de la interpretación de |f| en |A'| al resultado de mapear
%% |h| a |as|. La relación de igualdad correspondiente es la de la interpretación del sort
%% |s| en |A|:

Finally, let's define a type |Homomorphism| with a record with two fields: the
function between algebras, and the condition of homomorphism:

\begin{spec}
record Homomorphism (A : Algebra Σ) (A' : Algebra Σ) : Set _ where
  field
    ′_′    : A ⟿ A'
    cond   : ∀ {ty} (f : funcs Σ ty) → homCond A A' ′_′ f
\end{spec}

\noindent Note the use of the notation of the function homomorphism: If |H|
is an homomorphism, |′ H ′| is the field corresponding to the function
between algebras.


\subsection{Initial algebra and Term algebra}

\subsection*{Initial Algebra}

A $\Sigma$-algebra $\mathcal{A}$ is called \textbf{initial} if for all
$\Sigma$-algebra $\mathcal{B}$ there exists exactly one homomorphism from
$\mathcal{A}$ to $\mathcal{B}$.

In order to formalize the concept of initial algebra in Agda, we proceed to
define the notion of \textit{unicity} of an homomorphism. Informally, we can
say that an element $e \in E$ is unique if for all element $e' \in E$ the
equation $e = e'$ holds. We can generalize this definition to an arbitrary
equivalence relation, and we define the type |Unicity|:

\begin{spec}
Unicity : ∀ {ℓ₁} {ℓ₂} →  (A : Set ℓ₁) → (rel : Rel A ℓ₂) →
                         IsEquivalence rel → Set _ 
Unicity A _≈_ p = Σ[ a ∈ A ] ((a' : A) → a ≈ a')
\end{spec}

\noindent Given a type |A|, and a equivalence relation |_≈_| on |A|,
an element |a : A| is unique (except equivalence) with respect to |_≈_| if for all element
|a' : A|, |a| and |a'| are related by |_≈_|.

In order to define the equality of homomorphisms, let's define a type to represent the
property of extensional equality. If |A| and |B| are sets, |_≈A_| and |_≈B_| are binary relations
on |A| and |B| respectively, and |f| and |g| are functions from |A| to |B|, we define
the property |ExtProp|:

\begin{spec}
ExtProp _≈A_ _≈B_ f g = (a a' : A) → a ≈A a' → f a ≈B g a'
\end{spec}

Two homomorphisms |H| and |H'| are equals if the functions |′ H ′| and |′ H' ′| are
extensionally equals. Let's define the type |_≈ₕ_|:

\begin{spec}
data _≈ₕ_  {Σ} {A : Algebra Σ} {A' : Algebra Σ}
           (H H' : Homomorphism A A') : Set _ where
  ext :  ((s : sorts Σ) → ExtProp  (_≈_ (A ⟦ s ⟧ₛ)) (_≈_ (A' ⟦ s ⟧ₛ))
                                   (_⟨$⟩_ (′ H ′ s)) (_⟨$⟩_ (′ H' ′ s))) →
         H ≈ₕ H'
\end{spec}

The relation |_≈ₕ_| is an equivalence relation. We can prove this, but we don't
show the proof on this text:

\begin{spec}
equiv≈ₕ : ∀  {Σ} {A : Algebra Σ} {A' : Algebra Σ} →
              IsEquivalence (_≈ₕ_ {A = A} {A' = A'})
equiv≈ₕ = ...
\end{spec}


With all these definitions we can formalize the initial algebra of a signature |Σ|.
Let's define the type |Initial| with a record with two fields: The algebra and the
proof of initiality:

\begin{spec}
record Initial (Σ : Signature) : Set _ where
  field
    alg      : Algebra Σ
    init     : (A : Algebra Σ) → Unicity (Homomorphism alg A) (_≈ₕ_) equiv≈ₕ
\end{spec}


\subsection*{Term algebra}

From a signature $\Sigma$ can be defined an algebra called \textbf{term algebra}. The
carriers of each sort $s$ of $\Sigma$ are the terms generated by the function symbols
of $\Sigma$, with target sort $s$, called the \textit{ground terms} or \textit{Herbrand Universe}
of sort $s$. 

\begin{itemize}
\item Let $k$ be an operation with type $[] \rightarrow s$, $k \in HU_s$
\item Let $f$ be an operation with type $[s_1,...,s_n] \rightarrow s$ and
      $t_i \in HU_{s_i}$ for each $i$ such that $1 \leq i \leq n$, then $f\,(t_1,...,t_n) \in HU_s$
\end{itemize}

We can define this on Agda, with a type indexed on the sorts of the signature:

\begin{spec}
data HU (Σ : Signature) : (s : sorts Σ) → Set where
  term : ∀ {ar} {s} →  (f : funcs Σ (ar , s)) →
                       (ts : VecH (sorts Σ) (HU Σ) ar) → HU Σ s
\end{spec}

The type |HU Σ s| formalizes the definition of $HU_s$ that we saw previously:

\begin{itemize}
\item Let |k : funcs Σ ([] , s)|, then |term k ⟨⟩ : HU Σ s|.
\item Let |f : funcs Σ ([s₁ ,..., sₙ] , s)| and |ts = ⟨ t_1,...,t_n ⟩|, where
      |t₁ : HU Σ s₁| , ... ,|tₙ : HU Σ sₙ|, then |term f ts : HU Σ s|.
\end{itemize}

\paragraph{Example}
Let's define some terms of the signature |Σₑ|:

\begin{spec}
t₁ : HU Σₑ E
t₁ = term (valN 2) ⟨⟩

t₂ : HU Σₑ E
t₂ = term (varN " x ") ⟨⟩

t₃ : HU Σₑ E
t₃ = term plus (t₁ ▹ t₂ ▹ ⟨⟩)
\end{spec}

Let's define the term algebra of a signature $\Sigma$. The carrier of each sort $s$ is
the set $HU_s$. The interpretation of each operation with target sort $s$ is a term in
$HU_s$. This algebra is usually written $T(\Sigma)$.

\begin{spec}
∣T∣ : (Σ : Signature) → Algebra Σ
∣T∣ Σ = record  { _⟦_⟧ₛ = setoid ∘ HU Σ
                ; _⟦_⟧  = λ f → termFuns f
                }
  where termFuns f = record  { _⟨$⟩_ = term f
                             ; cong = ...
                             }
\end{spec}

\noindent We omit the proof of \textit{cong} in this text for simplicity.

In the rest of this section we show the formalization of the proof of initiality of
term algebra.

\subsection*{The term algebra is initial}

To prove that the term algebra is initial we must to give, for each $\Sigma$-algebra $\mathcal{A}$,
an unique homomorphism from $T(\Sigma)$ to $\mathcal{A}$. Let's define this homomorphism. Let $s$
be a sort of $\Sigma$:

\begin{itemize}
\item Let $k$ be an operation with empty arity and target sort $s$, then
      $h\,k\,=\,k_{\mathcal{A}}$
\item Let $f$ be an operation with type $[s_1,...,s_n] \rightarrow s$, then
      $h\,(f\,(t_1,...,t_n))\,=\,f_{\mathcal{A}}\,(h\,t_1,...,h\,t_n)$
\end{itemize}

We could formalize this homomorphism in the following way:

\begin{spec}
∣T∣→A : ∀ {A : Algebra Σ} (s : sorts Σ) → HU Σ s → Carrier (A ⟦ s ⟧ₛ)
∣T∣→A {A = A} s (term f ts) = A ⟦ f ⟧ ⟨$⟩ (mapV ∣T∣→A ts)
\end{spec}

\noindent However the termination checker of Agda can't ensure the termination.
We solve this defining two mutually recursive functions:

\begin{spec}
mutual
  ∣T∣→A : ∀ {Σ} {A : Algebra Σ} (s : sorts Σ) → HU Σ s → Carrier (A ⟦ s ⟧ₛ)
  ∣T∣→A {A = A} s (term {[]} f ⟨⟩) = A ⟦ f ⟧ ⟨$⟩ ⟨⟩
  ∣T∣→A {A = A} s (term {s₀ ∷ _} f (t₀ ▹ ts)) =
                 A ⟦ f ⟧ ⟨$⟩ (∣T∣→A s₀ t₀) ▹ map∣T∣→A ts


  map∣T∣→A :  ∀ {Σ} {A : Algebra Σ} {ar : Arity Σ} →
              VecH (sorts Σ) (HU Σ) ar →
              VecH (sorts Σ) (Carrier ∘ _⟦_⟧ₛ A) ar
  map∣T∣→A {ar = []} ⟨⟩ = ⟨⟩
  map∣T∣→A {ar = s₁ ∷ _} (t₁ ▹ ts₁) = ∣T∣→A s₁ t₁ ▹ map∣T∣→A ts₁
\end{spec}

\noindent Now, the termination checker accepts the definition.

With the function |∣T∣→A| we can define the homomorphism from the
term algebra to any other algebra:

\begin{spec}
∣T∣ₕ : ∀ {Σ} → (A : Algebra Σ) → Homomorphism (∣T∣ Σ) A
∣T∣ₕ A = record  { ′_′  = record  { _⟨$⟩_ = ∣T∣→A
                                  ; cong  = ...}
                 ; cond = ...}
\end{spec}

\noindent We don't show the proofs of congruence and condition of homomorphism in this
text.

By last, it only remains to prove the uniqueness of the homomorphism |∣T∣ₕ|. Given two
homomorphisms |h₁| and |h₂| from |∣T∣ Σ| to |A|, we must to prove that for each |term f ts : HU Σ s|
the following holds:

\begin{spec}
    ′ h₁ ′ s ⟨$⟩ term f ts
    ≈ₛ
    ′ h₂ ′ s ⟨$⟩ term f ts
\end{spec}

\noindent where |≈ₛ| is the equivalence relation of the interpretation of sort |s|
in |A|, i.e., |_≈_ A ⟦ s ⟧ₛ|.

Let's define the proof on Agda:

\begin{spec}
uni :  (h₁ : Homomorphism (∣T∣ Σ) A) →
       (h₂ : Homomorphism (∣T∣ Σ) A) →
       (s : sorts Σ) → (t₁ t₂ : HU Σ s) → t₁ ≡ t₂ →
       _≈_ (A ⟦ s ⟧ₛ) (′ h₁ ′ s ⟨$⟩ t₁) (′ h₂ ′ s ⟨$⟩ t₂)
uni h₁ h₂ s (term {ar} f ts) ._ refl =
                          begin
                            ′ h₁ ′ s ⟨$⟩ term f ts
                              ≈⟨ cond h₁ f ts ⟩
                            A ⟦ f ⟧ ⟨$⟩ (map⟿ ′ h₁ ′ ts)
                              ≈⟨ Π.cong (A ⟦ f ⟧) (mapV≡ ar ts) ⟩
                            A ⟦ f ⟧ ⟨$⟩ (map⟿ ′ h₂ ′ ts)
                              ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (cond h₂ f ts) ⟩ 
                            ′ h₂ ′ s ⟨$⟩ term f ts
                          ∎
                  where  mapV≡ :  (ar : Arity Σ) → (ts₀ : VecH (sorts Σ) (HU Σ) ar) →
                                 (mapV (_⟨$⟩_ ∘ ′ h₁ ′) ts₀) ∼v
                                 (mapV (_⟨$⟩_ ∘ ′ h₂ ′) ts₀)
                         mapV≡ = ...
\end{spec}

\noindent mapV≡ is the extension of |uni| to vectors, and is mutually recursive with
this.

