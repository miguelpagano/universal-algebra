\section{Universal Algebra}
\label{sec:univ-alg}

In this section we present our formalization in Agda of the core
concepts of heterogenouos universal algebra, up to initiality of the
term algebra, and some importants theorems.
As far as we know, there are two formalizations of
(multisorted) universal algebra: Capretta's implementation in Coq and
\citet{kahl-2011} formalization of allegories in Agda.

We will motivate some of the main definitions of the development and
show its more interesting parts, while ommiting some technical details.
The full code is available at \url{https://cs.famaf.unc.edu.ar/~mpagano/univ-alg/}.

We recall some basic definitions of multisorted
universal algebra following the
\textit{Handbook of Logic in Computer Science}, \cite{handbook}.

\paragraph{Signature}

A \emph{signature} is a pair of sets $(S,F)$, called \textit{sorts}
and \textit{operations} (or \textit{function symbols})
respectively. An operation is a triple $(f,[s_1,\ldots,s_n],s)$
consisting of a \textit{name}, a list of sorts (its \textit{arity)},
and another sort (its \textit{target sort}). We write operations as a
type declaration $f : [s_1,...,s_n] \Rightarrow s$ and say ``$f$ has
type $[s_1,...,s_n] \Rightarrow s$''.

There is one alternative way of specifying the operations, that
seems to us more type-theoretically, as a family of sets (of
operations) indexed by (their) types. We use a record to represent
signatures in Agda, the field |sorts| is a Set and |ops| is a family
of sets indexed by the types of operations:

\begin{spec}
record Signature : Set₁ where
  constructor ⟨_,_⟩
  field
    sorts  : Set
    ops  : List sorts × sorts → Set 

  Arity : Set
  Arity = List sorts
\end{spec}

\noindent This way of defining the set of operations offers two
advantages. On the one hand, we can have an infinite number of sorts
and also of operations; and, more important, we can naturally
define functions or predicates over operations of a given type.

As an example, consider a signature for a language with arithmetic
and boolean expressions:

\begin{spec}
data S : Set where
  nat  : S
  bool : S

data O : (List S) × S → Set where
  consℕ : (n : ℕ) → O ([] , nat)
  consB  : (b : Bool) → O ([] , bool)
  plus   : O (nat ∷ [ nat ] , nat)
  prod   : O (nat ∷ [ nat ] , nat)
  eq     : O (nat ∷ [ nat ] , bool)
  and    : O (bool ∷ [ bool ] , bool)
  or     : O (bool ∷ [ bool ] , bool)

Sig₁ : Signature
Sig₁ = ⟨ S , O ⟩

\end{spec}

\noindent We have a constant operation |consℕ n| for each natural
number |n|, two constants |consB true| and |consB false|, and binary
operations with diferent types. Note that, for example, we can define
functions or predicates only for binary operations of sort |nat|:

\begin{spec}
property : O (nat ∷ [ nat ] , nat) → P
property f = ...
\end{spec}

\noindent and if we do pattern matching over f, we have two posible
terms: |plus| and |prod|.

\paragraph{Algebra}

Usually, an \emph{algebra} $\mathcal{A}$ of a signature $\Sigma$, or a
$\Sigma$-algebra, consists of a family of sets indexed by the sorts of
$\Sigma$ and a family of functions indexed by the operations of
$\Sigma$. We use $\mathcal{A}_s$ for the \emph{interpretation} or the
\emph{carrier} of the sort $s$; given an operation $f \colon
[s_1,...,s_n] \Rightarrow s$, the interpretation of $f$ is a total
function $f_{\mathcal{A}}\colon \mathcal{A}_{s_1} \times ... \times
\mathcal{A}_{s_n} \rightarrow \mathcal{A}_s$.

In type-theory, is convenient to use setoids instead of sets,
representing the carrier of an algebra. We coincide with Capretta
in this point. Setoids allows to define an arbitrary equivalence
relation on a set, and it's easy to define congruence, quotient algebra
and subalgebras. With setoids we can define a carrier which
elements are functions, with the extensional equality as the relation
of the setoid.

As far as possible, we use the standard library
\citep*{danielsson-agdalib} definitions; for instance, setoids are
defined as a record with fields: the |Carrier : Set|, the
relation |_≈_ : Rel Carrier|, and the proof that |IsEquivalence _≈_|.
The operator | ∥_∥ | represents the forgetful functor from setoids
to sets, so that | ∥ (A,_≈A_,_) ∥ = A|.

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
\begin{spec}
data HVec {l} {I : Set}  (A : I -> Set l) :
                         List I → Set l where
  ⟨⟩  : HVec A []
  _▹_ : ∀  {i is} → (v : A i) →
           (vs : HVec A is) → HVec A (i ∷ is)
\end{spec}

When |A| is a family of setoids |I → Setoid|, and |is : List I|,  it
is straightforward to promote this construction to setoids and we
use |A ✳ is| to refer to the setoid of heterogeneous vectors indexed
in |is|, where the equivalence relation is the point-wisely induced.
The interpretation of the operation
$f \colon [s_1,…,s_n] \Rightarrow s$ should be a setoid morphism |A ✳
[s₁,…,sₙ] ⟶ A s|.


An algebra for a signature $\Sigma$ is a record with two fields: the
interpretation for sorts and the interpretation for operations.

\begin{spec}
record Algebra {ℓ₁ ℓ₂}  (Σ : Signature) :
                            Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  constructor _∥_
  field
    _⟦_⟧ₛ   : sorts Σ → Setoid ℓ₁ ℓ₂
    _⟦_⟧ₒ    : ∀  {ar s} → ops Σ (ar , s) →
                  _⟦_⟧ₛ ✳ ar ⟶ _⟦_⟧ₛ s

  _⟦_⟧ₛ* : (ar : Arity Σ) → Set _
  _⟦_⟧ₛ* ar = Carrier (HVecSet (sorts Σ) _⟦_⟧ₛ ar)
\end{spec}

Let see an example of a |Sig₁|-algebra. We interpret sorts |nat| and
|bool| with setoids |ℕ| and |Bool|, where the equivalence relation
is the definitional equality of Agda (the function |setoid| constructs
this trivial setoid).

\begin{spec}
iS : sorts Sig₁ → Setoid _ _
iS nat   = setoid ℕ
iS bool  = setoid Bool

iO : ∀  {ar s} → ops Sig₁ (ar ↦ s) →
        (iS ✳ ar) ⟶ iS s
iO (consℕ n) = record  { _⟨$⟩_ = λ { ⟨⟩ → n }
                       ; cong = ... }
iO (consB b) = record  { _⟨$⟩_ = λ {⟨⟩ → b}
                       ; cong = ... }
iO plus = record  { _⟨$⟩_ = λ {⟨⟨ n₁ , n₂ ⟩⟩ → n₁ + n₂}
                  ; cong = ... }
iO prod = record  { _⟨$⟩_ = λ {⟨⟨ n₁ , n₂ ⟩⟩ → n₁ * n₂}
                  ; cong = ... }
iO eq = record  { _⟨$⟩_ = λ {⟨⟨ n₁ , n₂ ⟩⟩ → n₁ =ₙ n₂}
                ; cong = ... }
iO and = record  { _⟨$⟩_ = λ {⟨⟨ b₁ , b₂ ⟩⟩ → b₁ ∧ b₂}
                 ; cong = ... }
iO or = record  { _⟨$⟩_ = λ {⟨⟨ b₁ , b₂ ⟩⟩ → b₁ ∨ b₂}
                ; cong = ... }
       
Alg₁ : Algebra Sig₁
Alg₁ = iS ∥ iO
\end{spec}

\noindent The interpretation of the operations of a signature are functions over setoids, so one must to provide a proof of preservation of
equalities (the field |cong|), we omit these proofs as they are utterly
uninteresting. The functions |_+_|, |_*_|, |_=ₙ_|, |_∧_| and |_∨_| are
the expected over |ℕ| and |Bool|.
It's interesting to note that Agda infers the types of each
interpretation function in |iO|. For example the interpretation of
|plus| is a function from the setoid of vectors of two elements of
type |ℕ|, to |ℕ| (we use the notation |⟨⟨ x , y ⟩⟩| to
represent the vector |x ▹ (y ▹ ⟨⟩)|).

\paragraph{Homomorphism}

Let $\mathcal{A}$ and $\mathcal{B}$ be two $\Sigma$-algebras, a \emph{homomorphism}
$h$ from $\mathcal{A}$ to $\mathcal{B}$ is a family of functions indexed by the
sorts $h_s : \mathcal{A}_s \rightarrow \mathcal{B}_s$,
such that for each operation $f : [s_1,...,s_n] \Rightarrow s$, the following holds:
\begin{equation}
  h_s(f_{\mathcal{A}}(a_1,...,a_n)) = f_{\mathcal{B}}(h_{s_1}\,a_1,...,h_{s_n}\,a_n)\label{eq:homcond}
\end{equation}

