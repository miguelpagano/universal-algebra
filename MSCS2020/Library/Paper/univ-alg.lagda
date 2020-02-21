% %"\newline\urlprefix\url{" url * "}" * write$ newline$ }
\section{Universal Algebra}
\label{sec:univ-alg}

In this section we present our formalization in Agda of the core
concepts of heterogeneous universal algebra; in the next two sections
we focus respectively on equational logic and signature morphisms.
Meinke' and Tucker's chapter~\cite{meinke-tucker-1992} is our
reference for heterogeneous universal algebra; we will recall some
definitions and state all the results we formalized. Bove et
al.~\cite{agda-intro} offer a gentle introduction to Agda; we expect
the reader to be familiar with Haskell or some other functional
language.

\subsection{Signature, algebra, and homomorphism}

\paragraph{Signature}

A \emph{signature} is a pair of sets $(S,F)$, called \textit{sorts}
and \textit{operations} (or \textit{function symbols}) respectively;
each operation is a triple $(f,[s_1,\ldots,s_n],s)$ consisting of a
\textit{name}, its \textit{arity}, and the \textit{target sort} (we
also use the notation $f \colon [s_1,...,s_n] \Rightarrow s$).

In Agda we use dependent records to represent signatures; in dependent
records the type of some field may depend on the value of a previous
one or parameters of the record. Type-theoretically one can take
operations (of a signature) as a family of sets indexed by the arity and target sort
(an indexed family of sets can also be thought as predicates over the
index set, an index satisfies the predicate if its family is
inhabited):
\begin{spec}
record Signature : Set₁ where
  field
    sorts  :   Set
    ops    :   List sorts × sorts → Set 
\end{spec}
\noindent |A × B| corresponds to the non-dependent cartesian product
of |A| and |B|.

In order to declare a concrete signature one first declares
the set of sorts and the set of operations, which are then bundled
together in a record.  For example, the mono-sorted signature of monoids has a
unique sort, so we use the unit type |⊤| with its sole constructor
|tt|. We define a family indexed on |List ⊤ x ⊤|, with two constructors,
corresponding with the operations: a 0-ary operation |e|, and a binary
operation |∙| (note that constructors can
start with a lower-case letter or any symbol):
\begin{spec}
data monoid-op : List ⊤ × ⊤ → Set where
   e : monoid-op ([ ] , tt)
   ∙ : monoid-op ( [ tt , tt ] , tt)
monoid-sig : Signature
monoid-sig = record { sorts = ⊤ ; ops = monoid-op }
\end{spec}
\noindent The signature of monoid actions has two sorts, one for the
monoid and the other for the set on which the monoid acts.
\begin{spec}
data actMonₛ : Set where
  mon : actMonₛ
  set : actMonₛ
data actMonₒ : List actMonₛ × actMonₛ → Set where
  e  : actMonₒ ([ ] , mon)
  *  : actMonₒ ([ mon , mon ] , mon)
  ∙  : actMonₒ ([ mon , set ] , set)
actMon-sig : Signature
actMon-sig = record { sorts = actMonₛ ; ops = actMonₒ }
\end{spec}

\noindent Defining operations as a family indexed by arities and
target sorts carries some benefits in the use of the library: as in
the above examples, the names of operations are constructors of a
family of datatypes and so it is possible to perform pattern matching
on them. Notice also that infinitary signatures can be represented in
our setting; in fact, all the results are valid for any signature, be
it finite or infinite.

We show two examples of signatures with infinite operations, the first
might be more appealing to computer scientists and the second is more
mathematical. The abstract syntax of a language for arithmetic expressions
may have one sort, a constant operation for each natural number and a
binary operation representing the addition of two expressions.
\begin{spec}
data Sortsₑ : Set where E : Sortsₑ
data Opsₑ : List Sortsₑ × Sortsₑ → Set where
  val   : (n : ℕ)   → Opsₑ ([] , E)
  plus  : Opsₑ ( E ∷ [ E ] , E )
\end{spec}

\noindent Vector spaces over a field can be seen as a heterogeneous signature
with two sorts~\cite{birkhoff-70} or as homogeneous signature
over the field \cite[p. 132]{birkhoff-40}; this latter approach can be
easily specified in our library, even if the field is infinite:
\begin{spec}
data Sorts-v Set where V : Sorts-v
data Ops-v (F : Set) : Set where
  _+_ : Ops-v ( V ∷ [ V ] , V )      -- vector addition
  ν  : (f : F) → Ops-v ( [ V ] , V)  -- scalar multiplication
vspace-sig : (F : Set) → Signature
vspace-sig F = record {sorts = Sorts-v ; ops = Ops-v F}
\end{spec}

\paragraph{Algebra}
An \emph{algebra} $\mathcal{A}$ for the signature $\Sigma$ consists of
a family of sets indexed by the sorts of $\Sigma$ and a family of
functions indexed by the operations of $\Sigma$. We use
$\mathcal{A}_s$ for the \emph{interpretation} or the \emph{carrier} of
the sort $s$; given an operation
$f \colon [s_1,...,s_n] \Rightarrow s$, the interpretation of $f$ is a
total function
$f_{\mathcal{A}}\colon \mathcal{A}_{s_1} \times ... \times
\mathcal{A}_{s_n} \rightarrow \mathcal{A}_s$. 
We formalize the product $\mathcal{A}_{s_1} \times ... \times
\mathcal{A}_{s_n}$ as \emph{heterogeneous vectors}. The
type of heterogeneous vectors is parameterized by a set |I|
and a family of sets indexed by |I|; and is indexed over a
list of |I|:
\begin{spec}
data HVec {I : Set}  (A : I → Set) : List I → Set where
  ⟨⟩    :  HVec A []
  _▹_   :  ∀  {i is} → A i → HVec A is → HVec A (i ∷ is)
\end{spec}
\noindent The first parameter |I| is implicit (written in braces), which means that Agda
will infer it by unification; notices that the constructor |_▹_| also
takes two implicit arguments (we use the notation |∀| to skip their
types). Let |Σ| be a signature and |A : sorts Σ → Set|, then the
product $\mathcal{A}_{s_1} \times ... \times \mathcal{A}_{s_n}$ is
formalized as |HVec A [s₁,…,sₙ]|.

We need one more ingredient to give the formal notion of algebras: the
mathematical definition of carriers assumes an underlying notion of
equality.  In type theory one makes it apparent by using setoids (\ie
sets paired with an equivalence relation), which were thoroughly
studied by Barthe et al.~\cite{barthe-setoids-2003}. Setoids are
defined in the standard library \cite{danielsson-agdalib} of
Agda\footnote{Our formalization is based on several concepts defined
  in the standard library.} as a record with three
fields.
\begin{spec}
record Setoid : Set₁ where
  field
    Carrier       : Set                     
    _≈_           : Carrier → Carrier → Set 
    isEquivalence : IsEquivalence _≈_       
\end{spec}
\noindent The relation is given as a family of types indexed over a pair
of elements of the carrier (|a b : Carrier| are related if the type |a
≈ b| is inhabited); |IsEquivalence _≈_| is again a record whose fields
correspond to the proofs of reflexivity, symmetry, and transitivity.

The finest equivalence relation over any set is given
by the \emph{propositional equality} which only equates each element with
itself, thus we can endow any set with a setoid structure with the function
|setoid : Set → Setoid| of the standard library; vice versa, there
is a forgetful functor | ∥_∥ : Setoid → Set | which returns the carrier.

Setoid morphisms are functions which preserve the equality:
\begin{spec}
record _⟶_ (A B : Setoid) : Set where
  field
  _⟨$⟩_ : ∥ A ∥ → ∥ B ∥
  cong : ∀ {a a'} → _≈_ A a a' → _≈_ B (_⟨$⟩ a) (_⟨$⟩ a')
\end{spec}
\noindent Notice that |_⟶_| is a record parameterized on two setoids.
The first field is the function, by declaring it mixfix one can
write |f ⟨$⟩ a| when |f : A ⟶ B| and |a : ∥ A ∥ |; the second field is
given by a function mapping equivalence proofs on the source setoid to
equivalence proofs on the target. Setoid morphisms will be used to
give the interpretation of operations.

Let |A : I → Set| be a family of sets and |P : {i : I} → A i → Set| a
family of predicates, we let |P * : ∀ {is} → HVec A is → Set| be the
point-wise extension of |P| over heterogeneous vectors. We also use
the point-wise extension to define the setoid of heterogeneous vectors
given a family of setoids |A : I → Setoid| and write |A ✳ is| for the
setoid of heterogeneous vectors with index |is|. Algebras are
formalized as records parameterized on the signature.
\begin{spec}
record Algebra (Σ : Signature) : Set₁  where
  field
    _⟦_⟧ₛ    : sorts Σ → Setoid
    _⟦_⟧ₒ    : ∀  {ar s} → (f : ops Σ (ar , s)) → _⟦_⟧ₛ ✳ ar ⟶ _⟦_⟧ₛ s
\end{spec}
\noindent If |A| is an algebra for the signature |monoid-sig|, then
|A ⟦ tt ⟧ₛ| is the carrier, |A ⟦ e ⟧ₒ| and |A ⟦ ∙ ⟧ₒ| are the interpretations
of the operations. We invite the interested reader to browse the examples to
see algebras for the signatures we have shown.

\paragraph{Homomorphism}
Let $\Sigma$ be a signature and let $\mathcal{A}$ and $\mathcal{B}$ be
algebras for $\Sigma$. A \emph{homomorphism} $h$ from $\mathcal{A}$ to
$\mathcal{B}$ is a family of functions indexed by the sorts
$h_s : \mathcal{A}_s \rightarrow \mathcal{B}_s$, such that for each
operation $f : [s_1,...,s_n] \Rightarrow s$, the following holds:
\begin{equation}
  h_s(f_{\mathcal{A}}(a_1,...,a_n)) = f_{\mathcal{B}}(h_{s_1}\,a_1,...,h_{s_n}\,a_n)\label{eq:homcond}
\end{equation}
\noindent Notice that this is a condition over the family of
functions.

In order to formalize homomorphisms we first introduce a
notation for families of setoid morphisms indexed over sorts:
\begin{spec}
_⟿_ : ∀ {Σ} → Algebra Σ → Algebra Σ → Set
_⟿_ {Σ} A B = (s : sorts Σ) → A ⟦ s ⟧ₛ ⟶ B ⟦ s ⟧ₛ
\end{spec}
\noindent We make explicit the implicit parameter |Σ| because
otherwise |sorts Σ| does not make sense.\footnote{In the library we
  use modules in order to avoid the repetition of the parameters |Σ|,
  |A|, and |B|.} To enforce \eqref{eq:homcond} we also define a
predicate over families of setoids morphisms:
\begin{spec}
homCond : ∀ {Σ} {A B} → A ⟿ B → Set
homCond {Σ} {A} {B} h = ∀ {ar s} (f : ops Σ (ar , s)) (as : ∥ A ⟦_⟧ₛ ✳ ar ∥) → 
         h s ⟨$⟩ (A ⟦ f ⟧ₒ ⟨$⟩ as) ≈ₛ B ⟦ f ⟧ₒ ⟨$⟩ map h as
\end{spec}
\noindent where |_≈ₛ_| is the equivalence relation of the setoid
|B ⟦ s ⟧ₛ| and |map h| is the obvious extension of |h| over vectors.
A homomorphism is a record parameterized by the source and target algebras
\begin{spec}
record Homo {Σ} (A B : Algebra Σ) : Set where
  field
    ′_′ : A ⟿ B
    cond : homCond ′_′
\end{spec}
\noindent As expected, we have the identity homomorphism |Idₕ A : Homo A A| and
the composition |G ∘ₕ F : Homo A C| of homomorphisms |F : Homo A B|
and |G : Homo B C|. It is also expected that |F ∘ₕ Idₕ A| and |F| are
equal in some sense. Since Agda is based on an
intensional type theory, we cannot take the definitional equality
(which distinguishes |id| from |λ n → n + 0| as functions
on naturals); instead, we equate setoid morphisms 
whenever their function parts are extensionally equal:
\begin{spec}
  _≈→_ : (f g : A ⟶ B) → Set
  f ≈→ g  = ∀ (a : ∥ A ∥) → (f ⟨$⟩ a) ≈B (g ⟨$⟩ a)
\end{spec}
\noindent Two homomorphisms are equal when their corresponding setoid
morphisms are extensionally equal:
\begin{spec}
  _≈ₕ_  : ∀ {Σ} {A B} → Homo A B → Homo A B → Set
  F ≈ₕ F' = (s : sorts Σ) → ′ F ′ s ≈→ ′ F' ′ s
\end{spec}
\noindent With respect to this equality, it is straightforward to
prove the associativity of the composition |_∘ₕ_| and that |Idₕ| is
the identity for the composition.
% \comment{It is straightforward to define the product |A₁ × A₂| of algebras |A₁|
% and |A₂| and the projection homomorphisms |Πᵢ : Homo (A₁ × A₂) Aᵢ| where
% |′ Πᵢ ′ _ ⟨$⟩ p = projᵢ p|.}
\subsection{Quotient and subalgebras}
In order to prove the more basic results of universal algebra, we need
to formalize subalgebras, congruence relations, and quotients.

\paragraph{Subalgebra}

A subalgebra $\mathcal{B}$ of an algebra $\mathcal{A}$ consists of a
family of subsets $\mathcal{B}_s \subseteq \mathcal{A}_s$, that are
closed under the interpretation of operations; that is, for every
$ f : [s_1, \ldots,s_n] \Rightarrow s$ the following condition holds
\begin{equation}
(a_1,\ldots,a_n) \in \mathcal{B}_{s_1} \times \cdots \times\mathcal{B}_{s_n}   \text{ implies }
  f_\mathcal{A}(a_1,\ldots,a_n) \in \mathcal{B}_{s} \enspace .
 \label{eq:opclosed}
\end{equation} 
\noindent As shown by Salvesen and Smith \cite{salvesen-subsets},
subsets cannot be added as a construction in intensional type theory
because they lack desirable properties. If |A : Set| and |P : A → Set|
is a predicate over |A|, then one can represent the subset containing the
elements on |A| that satisfy |P| as the dependent sum\footnote{Do not confuse
the syntax |Σ[_∈_]_| of dependent sum, with a variable |Σ : Signature|}
|Σ[ a ∈ A ] P| whose inhabitants are
pairs |(a , p)| where |a : A| and |p : P a|.\comment{This is not so
  pleasant as there can be several proofs of |P a|.} Let us consider a
setoid |A| and a predicate on its carrier |P : ∥ A ∥ → Set|; first
notice that we can lift the subset construction to setoids, defining
the equivalence relation |(a , q) ≈ (a' , q')| iff |a ≈ a'|.
Moreover, we might assume that |P| is \emph{well-defined},
which means that |a ≈A a'| and |P a| imply
|P a'|.
\begin{spec}
  WellDef : (A : Setoid) → (P : ∥ A ∥ → Set) → Set
  WellDef A P = ∀ {a a'} → a ≈A a' → P a → P a'
\end{spec}
\noindent A family of well-defined predicates will induce a subalgebra;
but we still need to formalize the condition \eqref{eq:opclosed}.  Let
|Σ| be a signature and |A| be an algebra for |Σ|.
\begin{spec}
    opClosed : (P : (s : sorts Σ) → ∥ A ⟦ s ⟧ₛ∥ → Set) → Set
    opClosed P = ∀ {ar s} (f : ops Σ (ar , s)) → (P * ⟨→⟩ P s) (A ⟦ f ⟧ₒ ⟨$⟩_)
\end{spec}
\noindent |(Q ⟨→⟩ R) f| can be read as the pre-condition |Q| implies
post-condition |R| after applying |f|; so |opClosed P f| asserts that if a vector |a*|
satisfies the predicate |P|, then the application of the interpretation |A ⟦ f ⟧ₒ|
to |a*| satisfies |P|, according to Eq.~\eqref{eq:opclosed}.
In summary, given an algebra
|A| for the signature |Σ| and a family |P| of predicates, such that |P
s| is well-defined for every sort |s| and |P| is |opClosed|, we can
define the |SubAlgebra A P| 
\begin{spec}
SubAlgebra : ∀ {Σ} A P → WellDef P → opClosed P → Algebra Σ
\end{spec}
\noindent In the subalgebra, an operation |f| is interpreted by
applying the interpretation of |f| in |A| to the first components of
the argument (and use the fact that |P| is op-closed to show that
the resulting value satisfies the predicate of the target sort).

\paragraph{Congruence and Quotients}
A \emph{congruence} on a $\Sigma$-algebra
$\mathcal{A}$ is a family
$Q$ of equivalence relations indexed by sorts, and each of them is
closed under the operations of the algebra. This condition is called
\emph{substitutivity} and can be formalized using the point-wise
extension of $Q$ over vectors: for every operation $ f : [s_1,
\ldots,s_n] \Rightarrow s$
\begin{equation}
  (\vec{a},\vec{b}) \in Q_{s_1} \times \cdots \times Q_{s_n} \text{ implies }
 (f_{\mathcal{A}}(\vec{a}) , f_{\mathcal{A}}(\vec{b})) \in Q_s\label{eq:congcond}
\end{equation} 

As with predicates, we say that a binary relation over a setoid is
well-defined if it is preserved by the setoid equality; this notion
can be extended over families of relations in the obvious way. In our
formalization, a congruence on an algebra |A| is a family |Q| of
well-defined, equivalence relations. The substitutivity condition
\eqref{eq:congcond} is aptly captured by the generalized containment
operator |_=[_]⇒_| of the standard library, where |P =[ f ]⇒ Q| if,
for all |a,b ∈ A|, |(a,b) ∈ P| implies |(f a, f b) ∈ Q|.
\begin{spec}
record Congruence (A : Algebra Σ) : Set where
  field
    rel : (s : sorts Σ) → (∥ A ⟦ s ⟧ₛ ∥ → ∥ A ⟦ s ⟧ₛ ∥ → Set)
    welldef : (s : sorts Σ) → WellDefBin (rel s)
    cequiv : (s : sorts Σ) → IsEquivalence (rel s)
    csubst : ∀ {ar s} → (f : ops Σ (ar , s)) → rel * =[ A ⟦ f ⟧ₒ ⟨$⟩_  ]⇒ rel s
\end{spec}

Given a congruence $Q$ over the algebra $\mathcal{A}$, we can obtain a
new algebra, the \emph{quotient algebra}, by interpreting the sort $s$
as the set of equivalence classes $\mathcal{A}_s / Q$; the condition
\eqref{eq:congcond} ensures that the operation $ f : [s_1, \ldots,s_n]
\Rightarrow s$ can be interpreted as the function mapping the vector
$([a_1],\ldots,[a_n])$ of equivalence classes into the class $[
f_\mathcal{A}(a_1,\ldots,a_n)]$. In Agda, we take the same carriers
from |A| and use |Q s| as the equivalence relation over |∥ A ⟦ s ⟧ₛ
∥|; operations are interpreted just as in |A| and the congruence proof
is given by |csubst Q|.

\paragraph{Isomorphism Theorems} The definitions of subalgebras,
quotients, and epimorphisms (surjective homomorphisms) are related by
the three isomorphism theorems. Although there is some small overhead
by the coding of subalgebras, the proofs follow very close what one would
do in paper. For proving these results we also defined the
\emph{kernel} and the \emph{homomorphic} image of homomorphisms.

\begin{theorem}[First isomorphism theorem] If $h : \alg{A} \rightarrow \alg{B}$
is an epimorphism, then $\alg{A} /\! \mathop{ker} h \simeq \alg{B}$.
\end{theorem}
\noindent Remember that the quotient $\alg A /\! \mathop{ker} h$ has
the same carrier as $\alg A$, so $h$ counts as the underlying function
and it respects the equivalence relation $\mathop{ker} h$ by
definition. Clearly $h$ is surjective and its injectivity is obvious.

\begin{theorem}[Second isomorphism theorem] If $\phi,\psi$ are congruences over $\alg A$,
such that $\psi \subseteq \phi$, then $(\alg A / \phi) \simeq (\alg A / \psi)/(\phi / \psi)$. 
\end{theorem}

\noindent In order to prove this theorem, we first prove that
$\phi / \psi$ is a congruence over $\alg A / \psi$: it suffices to
prove the well-definedness of $\phi / \psi$, \ie that
$(a,c) \in \psi$, $(b,d) \in \psi$, and $(a,b) \in \phi$ imply
$(c,d) \in \phi$; an obvious consequence of $\psi \subseteq
\phi$. Notice that the underlying carriers are the same in both cases:
those of $\alg A$, so the identity function is the mediating
isomorphism and the proof that it satisfies the homomorphism condition
is trivial.

\begin{theorem}[Third isomorphism theorem] Let $\alg B$ be a
subalgebra of $\alg A$ and $\phi$ be a congruence over $\alg A$. Let
$[\alg B]^{\phi}=\{K \in A / \phi : K \cap B \not= \emptyset\}$ and
let $\phi_B$ be the restriction of $\phi$ to $\alg B$, then
\begin{enumerate*}[label= (\roman*),itemjoin={}]
\item$\phi_B$ is a congruence over $\alg B$;
\item$[\alg B]^{\phi}$ is a subalgebra of~$\alg A$; and,
\item$[\alg B]^{\phi} \simeq \alg B / \phi_B$.
\end{enumerate*}
\end{theorem}
\noindent First we define the \emph{trace} of the congruence $\phi$ on
the subalgebra $\alg B$ as the restriction of $\phi$ on $\alg B$;
proving that it is a congruence over $\alg B$ involves some
bureaucracy (remember that an element of a subalgebra is a pair
$(a, p)$ such that $a \in A$ and $p$ is the proof that $a$ satisfies
the predicate defining $B$). For the second item, we model
$[\alg B]^{\phi}$ as a predicate over $\alg A$; it is satisfied by
$a \in A$ if there is some $b \in B$ such that $(a,b) \in \phi$. The
well-definedness of this predicate is easy (assuming $(a,a') \in \phi$
and $b\in B$ with $(a,b) \in \phi$, one can easily prove that
$(a',b) \in \phi$, thus $b$ is also the witness for proving that $a'$
satisfies the predicate). To prove that the predicate is closed under
the operations we take a vector of triples $(as,bs,ps)$ consisting of
a vector of elements in $A$, a vector of elements in $B$, and the
proofs $ps$ proving that $(as_i,bs_i)\in\phi$. Let $f$ be an
operation, since $B$ is closed we know $f(b_1,\ldots,b_n)\in B$ and
because $\phi$ is also closed we deduce
$(f(a_1,\ldots,a_n),f(b_1,\ldots,b_n))\in\phi$. Finally, the
underlying function witnessing the isomorphism
$[\alg B]^{\phi} \simeq \alg B / \phi_B$ is given by composing the
second projection with the first projection, thus getting an element
in $B$.

\subsection{The Term Algebra is initial}

A $\Sigma$-algebra $\mathcal{A}$ is called \emph{initial} if for any
$\Sigma$-algebra $\mathcal{B}$ there exists exactly one homomorphism
from $\mathcal{A}$ to $\mathcal{B}$. We give an abstract definition of
this universal property, existence of a unique element, for any set
|A| and any relation |R|
\begin{spec}
hasUnique {A} _≈_ = A × (∀ a a' → a ≈ a')
\end{spec}
\noindent and initiality can be formalized directly:
\begin{spec}
Initial : ∀ {Σ} → Algebra Σ → Set
Initial {Σ} A = ∀ (B : Algebra Σ) → hasUnique (_≈ₕ_ A B)
\end{spec}
Given a signature $\Sigma$ we can define the \emph{term algebra}
$\mathcal{T}$, whose carriers are sets of well-typed words built up
from the function symbols.  Sometimes this universe is called the
\emph{Herbrand Universe} and is inductively defined:
\begin{prooftree}
\AxiomC{$t_1 \in \mathcal{T}_{s_1}$}
\AxiomC{$\cdots$}
\AxiomC{$t_n \in \mathcal{T}_{s_n}$}
\RightLabel{$f : [s_1,...,s_{n}] \Rightarrow s$}
\TrinaryInfC{$f\,(t_1,...,t_{n}) \in \mathcal{T}_s$}
\end{prooftree}
\noindent This inductive definition can be written directly in Agda:
\begin{spec}
  data HU {Σ : Signature} : (s : sorts Σ) → Set where
    term : ∀  {ar s} → (f : ops Σ (ar ↦ s)) → HVec HU ar → HU s
\end{spec}
\noindent We use propositional equality to turn each |HUₛ| into a
setoid, thus completing the interpretation of sorts. To interpret an
operation $f \colon [s_1,\ldots,s_n] \Rightarrow s$ we map the vector
|⟨t₁,…,tₙ⟩ : HVec HU [s₁,…,sₙ]| to |term f ⟨t₁,…,tₙ⟩|; we omit
the proof of |cong|, which is too long and tedious to be
shown.
\begin{spec}
  ∣T∣ : (Σ : Signature) → Algebra Σ
  ∣T∣ Σ = record  { _⟦_⟧ₛ = setoid ∘ (HU {Σ}) ; _⟦_⟧ₒ  = ∣_|ₒ }
    where | f ∣ₒ = record { _⟨$⟩_ = term f ; cong = ... }
\end{spec}
\noindent Terms can be interpreted in any algebra
$\mathcal{A}$, yielding an homomorphism $h_A \colon \mathcal{T}
\to \mathcal{A}$
\[
  h_A (f(t_1,\ldots,t_n)) = f_{\mathcal{A}}\,(h_A\,t_1,...,h_A\,t_n) \enspace .
\] 
\noindent We cannot translate this definition directly in Agda, instead
we have to mutually define | ∣h∣→A | and its extension over vectors
| ∣h*∣→A| 
\begin{spec}
  ∣h∣→A : ∀ {Σ} → (A : Algebra Σ) → {s : sorts Σ} → HU s → ∥ A ⟦ s ⟧ₛ ∥
  ∣h∣→A A (term f ts) = A ⟦ f ⟧ₒ ⟨$⟩ (∣h*∣→A ts)
\end{spec}
\noindent It is straightforward to prove that |∣h∣→A| preserves
propositional equality and satisfies the homomorphism condition by
construction. To finish the proof that | ∣T∣ Σ | is initial, we prove,
by recursion on the structure of terms, that any pair of homomorphisms
are extensionally equal.


%%  LocalWords:  Agda equational morphisms Haskell homomorphism arity
%%  LocalWords:  cartesian monoids monoid tt sig actMon mon arities
%%  LocalWords:  datatypes infinitary parameterized HVec setoids et
%%  LocalWords:  Barthe al Setoid isEquivalence IsEquivalence setoid
%%  LocalWords:  reflexivity versa functor cong mixfix ar homcond
%%  LocalWords:  homomorphisms homCond cond intensional definitional
%%  LocalWords:  extensionally associativity