\section{Universal Algebra}

We present a formalisation of some concepts of Universal Algebra, included the proof
of initiality of the term algebra, in Agda.

\paragraph{Agda}
Agda is a functional programming language with dependent types, based on the
Martin Löf's intuitionistic type theory...

We show the main definitions of the development, ommiting some technical details.
The full code is available to download on \url{https://git.cs.famaf.unc.edu.ar/semantica-de-la-programacion/algebras-universales/UnivAlgebra.agda}.

The definitions that we present in this section are based on the \textit{Handbook of Logic in Computer Science}, (\cite{handbook}).

\subsection{Signature, algebra and homomorphism}

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
open import Data.List
open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open import Data.String
open import Data.Fin

open import VecH

open Setoid

\end{code}
%endif

A \textbf{signature} is a pair $(S,F)$ of sets, called \textit{sorts} and \textit{operations} (or \textit{function symbols}) respectively. An operation is a 3-uple $(w,[s_1,...,s_n],s)$ that consists of a \textit{name}, a list of sorts, and another sort, usually writed $(w : [s_1,...,s_n] \rightarrow s)$. The list of sorts $[s_1,...,s_n]$ is called \textit{arity}, the sort $s$ is called the \textit{target sort} and \textit{type} is the pair $([s_1,...,s_n],s)$. \footnote{In the bibliography of heterogeneous universal algebras the notion of arity may change. In the handbook is called \textit{arity} to what we call \textit{type}.}

We define signature in Agda, with a record with two fields. |sorts| is a Set and
|funcs| is a family of sets indexed in the types of operations:

\begin{code}
Sorts : Set _
Sorts = Set

Funcs : Sorts → Set _
Funcs S = (List S) × S → Set
 
record Signature : Set₁ where
  field
    sorts  : Sorts
    funcs  : Funcs sorts

  Arity : Set
  Arity = List sorts

  Type : Set
  Type = List sorts × sorts
\end{code}

An adventage of defining signature of this way is that the type system of Agda
allows to define properties of operations of a given arity. I.e., we can define a type
in Agda referring to the operations of a particular arity or type. This approach is
more type-theoretic than defining the operations with a list of arities, like in
\cite{capretta-99}, and we'll see some important adventages when we define the
translation of signatures.

We show two examples of signatures. The second one shows the posibility of define
a signature with infinite operations.

\paragraph{Example 1} A language with natural and boolean expressions.

\begin{code}
data S : Sorts where
  bool : S
  nat  : S

data F : Funcs S where
  fzero  : F ([] , nat)
  fsuc   : F ([ nat ] , nat)
  ftrue  : F ([] , bool)
  ffalse : F ([] , bool)
  feq    : F (nat ∷ [ nat ] , bool)

Σ₁ : Signature
Σ₁ = record  { sorts = S
             ; funcs = F
             }
\end{code}

\paragraph{Ejemplo 2} The language of arithmetic expressions that we present at introduction.

%include ejemplo2.lagda

\noindent Note that we have infinite function symbols, one for each natural number (constructor |valN|), and
one for each variable (contructor |varN|).

\subsection*{Algebra}

Let $\Sigma$ be a signature, an \textbf{algebra} $\mathcal{A}$ of $\Sigma$, or a $\Sigma$-algebra, consists
of a family of sets indexed on the sorts of $\Sigma$, called the \textit{carriers} (or \textit{sorts interpretation})
of $\mathcal{A}$ (we call $\mathcal{A}_s$ the carrier of the sort $S$ in $\mathcal{A}$), and for each operation
$w$ with type $[s_1,...,s_n],s$ a total function $w_A : \mathcal{A}_{s_1} \times ... \times \mathcal{A}_{s_n} \rightarrow \mathcal{A}_s$.
We call \textit{interpretation} of $w$ to this function.

We proceed to define the interpretation of sorts. Let's considere the algebra corresponding
to the semantics of the expressions language that we introduced previoulsy. For each expression, the semantics
is a function from states to natural numbers. Thus, each element of the interpretation of the sort of
the expressions will be a function, and we have an issue to define equality of this elements in Agda. Two
functions extensionally equal (i.e., pointwise equality) are not propositionally equals in Agda, so if we
implement the carrier of sorts with Sets we lose the equality of functions.

We use \textbf{setoids}, so we can represent a set with an arbitrary equivalence relation.

\paragraph{Setoids} blabla


Let's define the interpretation of sorts (or carriers):

\begin{code}
ISorts : ∀ {ℓ₁ ℓ₂} → (Σ : Signature) → Set _
ISorts {ℓ₁} {ℓ₂} Σ = (sorts Σ) → Setoid ℓ₁ ℓ₂
\end{code}

\noindent An element in |ISorts Σ s| is a setoid, and it represents the interpretation of sort
|s| in a |Σ|-algebra.

In order to define the interpretation of a function symbol $f$, with type $[s_1,...,s_n] \rightarrow s$,
in a $\Sigma$-algebra $\mathcal{A}$, we have to define a total function with domain
$\mathcal{A}_{s_1} \times ... \times \mathcal{A}_{s_n}$ and codomain $\mathcal{A}_{s}$. We use
\textit{vectors} to implement the domain of function interpretations, but this vectors will
contain element of different types, according to the arity. We define the type of
\textit{heterogeneous vectors}.

\paragraph{Heterogeneous vectors} blablabla

Let's define the interpretation of operations. Let $f$ be an operation with type $ty$,
and let $is$ be the interpretation of sorts; the interpretation of $f$ is a function
from the setoid of heterogeneous vectors to the interpretation of the target sort of
$f$:

\begin{code}
IFuncs :  ∀ {ℓ₁ ℓ₂} → (Σ : Signature) → (ty : ΣType Σ) →
          ISorts {ℓ₁} {ℓ₂} Σ → Set _
IFuncs Σ (ar , s) is = VecSet (sorts Σ) is ar ⟶ is s
\end{code}

\noindent Note that an element in |IFuncs Σ (ar , s) is| is a function between setoids.

Let's define the type of $\Sigma$-algebras, with a record with two fields, one corresponding
to the interpretation of sorts, and another to the interpretation of operations:

\begin{code}
record Algebra {ℓ₁ ℓ₂ : Level}  (Σ : Signature) :
                                Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  constructor _∥_
  field
    _⟦_⟧ₛ    : ISorts {ℓ₁} {ℓ₂} Σ
    _⟦_⟧    : ∀ {ty : ΣType Σ} → (f : funcs Σ ty) → IFuncs Σ ty _⟦_⟧ₛ
\end{code}

We use a convenient notation for fields. The interpretation of sort |s| in
|A| is writed |A ⟦ s ⟧ₛ|, and the interpretation of an operation |w|, |A ⟦ w ⟧|.


We define too a type representing the domain of an interpretation of function symbol,
wich will be useful in later definitions.
If |ar| is the arity of an operation |f|, the interpretation will be a function between
setoids, with domain the heterogeneous vectors with arity |ar| and interpretation |_⟦_⟧ₛ A|:

\begin{spec}
_⟦_⟧ₛ* : ∀ {Σ} {ℓ₁} {ℓ₂}  → (A : Algebra {ℓ₁} {ℓ₂} Σ)
                          → (ar : Arity Σ) → Set _
_⟦_⟧ₛ* {Σ} A ar = Carrier (VecSet (sorts Σ) (_⟦_⟧ₛ A) ar)
\end{spec}

\medskip

Let see an example of a |Σₑ|-algebra, the semantics of the expression language that we
introduced previously.

\paragraph{Example} Let's define the |Σₑ|-algebra |Semₑ|. The elements of the carrier
will be functions from states to natural numbers. 

\begin{spec}
State : Set
State = Var → ℕ
\end{spec}


\begin{spec}
iSortsₑ : ISorts Σₑ
iSortsₑ E = State →-setoid ℕ
\end{spec}

\noindent The function |→-setoid| allows us to define a function between two trivial
setoids, where the equivalence relation is the extensional equality.

Let's define the interpretation of each operation. Like we saw previously, a function
between setoids consists of two fields: the function of carriers, and de proof of
congruence (if two elements are related, the elements resulting of applying the function
are related too). We ommit this proof in this text.

For each |n : ℕ| we have an operation |valN n|. The arity is empty and the target sort is
|E|:

\begin{spec}
iValN : (n : ℕ) → IFuncs Σₑ ([] , E) iSortsₑ
iValN n = record  { _⟨$⟩_ = λ { ⟨⟩ σ → n }
                  ; cong = ... }
\end{spec}

The operation |plus| has type |(E ∷ [ E ] , E)|. So, the interpretation will be a
function from vectors of two elements of type |State → ℕ| to |State → ℕ|:

\begin{spec}
iPlus : IFuncs Σₑ (E ∷ [ E ] , E) iSortsₑ
iPlus = record  { _⟨$⟩_ = λ { (v₀ ▹ v₁ ▹ ⟨⟩) σ → v₀ σ + v₁ σ }
                ; cong = ... }
\end{spec}

By last, for each variable |v| we have an operation |varN v|, with empty arity and
target sort |E|. The interpretation is a function from empty vectors (corresponding to
empty arity) to |State → ℕ| (corresponding to the interpretation of |E|). This function
is the application of state to the variable |v|:

\begin{spec}
iVarN : (v : Var) → IFuncs Σₑ ([] , E) iSortsₑ
iVarN v = record  { _⟨$⟩_ = λ { ⟨⟩ σ → σ v }
                  ; cong = ... }
\end{spec}

So, we can define the |Semₑ| algebra:

\begin{spec}
iFuncsₑ : ∀ {ty} → (f : funcs Σₑ ty) → IFuncs Σₑ ty iSortsₑ
iFuncsₑ (valN n) = iValN n
iFuncsₑ plus = iPlus
iFuncsₑ (varN v) = iVarN v
\end{spec}

\begin{spec}
Semₑ : Algebra Σₑ
Semₑ = iSortsₑ ∥ iFuncsₑ
\end{spec}

\subsection*{Homomorphism}

Let $\mathcal{A}$ and $\mathcal{B}$ be two $\Sigma$-algebras, a \textbf{homomorphism}
$h$ from $\mathcal{A}$ to $\mathcal{B}$ is a indexed family $h_s : \mathcal{A}_s \rightarrow \mathcal{B}_s$,
such that for each operation $w$ with type $([s_1,...,s_n],s)$, the following holds:

\begin{center}
  $h_s(f_{\mathcal{A}}(a_1,...,a_n)) = f_{\mathcal{B}}(h_{s_1}\,a_1,...,h_{s_n}\,a_n)$ \;\;\;(1)
\end{center}

Let's define first the notion of \textit{function between} $\Sigma$\textit{-algebras}:

\begin{spec}
_⟿_ : ∀  {Σ : Signature}  →
         (A : Algebra Σ) → (A' : Algebra Σ) →
         Set _
_⟿_ {Σ} A A' = (s : sorts Σ) → A ⟦ s ⟧ₛ ⟶ A' ⟦ s ⟧ₛ
\end{spec}

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

