\section{Universal Algebra}
\label{sec:univ-alg}

In this section we present our formalization in Agda of the core
concepts of heterogenouos universal algebra; in the next two sections
we focus respectively on equational logic and signature morphisms.

Meinke' and Tucker's chapter \cite{meinke-tucker-1992} is our
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
Semantically, the sorts will be interpreted as sets and the
function symbols as operations.

In Agda we use dependent records (meaning that the type of some field
may depend on the value of a previous one) to represent signatures.
Type-theoretically one can take operations as a family of sets indexed
by the arity and target sort, |A × B| corresponds to the
non-dependent cartesian product of |A| and |B|.
\begin{spec}
record Signature : Set₁ where
  field
    sorts  :   Set
    ops    :   List sorts × sorts → Set 
\end{spec}
\noindent In order to declare a concrete signature one first declares
the set of sorts and the set of operations, which are then bundled
toghether in a record. For the mono-sorted signature of monoids has
one sort --|tt| is the only element of the unit type |⊤|-- and two
operations (note that constructors can start with a lower-case
letter or a symbol).
\begin{spec}
data monoid-op : List ⊤ × ⊤ → Set where
   e : monoid-op ([ ] , tt)
   ∙ : monoid-op ( tt ∷ [ tt ] , tt)
monoid-sig : Signature
monoid-sig = record { sorts = ⊤ ; ops = monoid-op }
\end{spec}
\noindent The signature of monoid actions has two sorts, one for the
monoid and the other for the set on which the monoid acts (we declare
both constructors in the same line).
\begin{spec}
data actMonₛ : Set where mon set : actMonₛ
data actMonₒ : List actMonₛ × actMonₛ → Set where
  e  : actMonₒ ([ ] , mon)
  *  : actMonₒ (mon ∷ [ mon ] , mon)
  ∙  : actMonₒ (mon ∷ [ set ] , set)
actMon-sig : Signature
actMon-sig = record { sorts = actMonₛ ; ops = actMonₒ }
\end{spec}
\noindent Defining operations as a family indexed by arities and target sorts
carries some benefits in the use of the library: as in the above
examples, the names of operations are constructors of a family of
datatypes and so it is possible to perform pattern matching on
them. Notice also that infinitary signatures can be represented in our
setting; in fact, all the results are valid for any signature, be it
finite or infinite.

\paragraph{Algebra.}

An \emph{algebra} $\mathcal{A}$ for the signature $\Sigma$ consists of
a family of sets indexed by the sorts of $\Sigma$ and a family of
functions indexed by the operations of $\Sigma$. We use
$\mathcal{A}_s$ for the \emph{interpretation} or the \emph{carrier} of
the sort $s$; given an operation
$f \colon [s_1,...,s_n] \Rightarrow s$, the interpretation of $f$ is a
total function
$f_{\mathcal{A}}\colon \mathcal{A}_{s_1} \times ... \times
\mathcal{A}_{s_n} \rightarrow \mathcal{A}_s$. What this definitions
hides is that carriers are pairs of a set and its equality; in
type-theory one makes this structure apparent by using Bishop's sets
(\ie sets paired with an equivalence relation) as the interpretation
of sorts. In type-theory Bishop's sets are better known as setoids and
they were thoroughly studied by Barthe et
al.~\cite{barthe-setoids-2003}. Setoids are defined in the the
standard library \cite{danielsson-agdalib} of Agda, which we
conveniently use as far as possible, as a record with three fields.
\begin{spec}
record Setoid : Set₁ where
  field
    Carrier       : Set                     
    _≈_           : Carrier → Carrier → Set 
    isEquivalence : IsEquivalence _≈_       
\end{spec}
\noindent The relation is given as family of types indexed over a pair
of elements of the carrier (|a b : Carrier| are related if the type |a
≈ b| is inhabited); |IsEquivalence _≈_| is again a record whose fields
correspond to the proofs of reflexivity, symmetry, and transitivity. A
proof of reflexivity of |_≈_| is given by a function with type |(a :
Carrier) → a ≈ a|; \ie a method that for each |a : Carrier| produces a
proof for |a ≈ a|. The operator | ∥_∥ | represents the forgetful
functor from setoids to sets, so that | ∥ (A,_≈A_,_) ∥ = A|. There is
an obvious functor |setoid : Set → Setoid| which maps a type |A| to
the setoid defined by the propositional equality over that type. In
the standard library it is also defined the point-wise extension of
two setoids |A ×-setoid B|.

Once sorts are interpreted as setoids, operations should be
interpreted as setoid morphisms; \ie functions which preserve the
equivalence relation.  Given setoids |A| and |B|, the type
|A ⟶ B| corresponds to morphism from |A| to |B| whose inhabitants are
records with fields |_⟨$⟩_ : ∥A∥ → ∥B∥| and |cong : ∀ a a' → a ≈A a' →
_⟨$⟩_ a ≈B _⟨$⟩_ a'|. Setoid morphisms will also play a role in the
definition of homomorpisms between algebras and some theorems will say
that two homomorphisms are equal; working in an intensional
type-theory, this equality cannot be taken as the definitional
equality. Of course, we equate morphisms |f , g : A ⟶ B|,
whenever the function parts of |f| and |g| are extensionally equal:
\begin{spec}
  _≈→_ : Rel (A ⟶ B)
  f ≈→ g  = ∀ (a : ∥ A ∥) → (f ⟨$⟩ a) ≈B (g ⟨$⟩ a)
\end{spec}%
\comment{\noindent It is immediate to prove that this relation is of equivalence.}%
Predicates over setoids should also be even over equal elements; thus we
set
\begin{spec}
  WellDef : (A : Setoid) → Pred (∥ A ∥) → Set
  WellDef A P = ∀ {a a'} → a ≈A a' → P a → P a'
\end{spec}
\noindent If |P| is well-defined, we deduce |P a ↔ P a'| if |a ≈
a'|, because equality is symmetric. Notice also that we can
define that a relation is well-defined using the product of 
setoids:
\begin{spec}
  WellDefBin : (A : Setoid) → Rel (∥ A ∥) → Set
  WellDefBin A R = WellDef (A ×-setoid A) (λ {(a , b) → R a b}) 
\end{spec}%
\comment{\noindent Expanding this definition we discover that |WellDefBin A R|
iff for all |a₁ ≈A a₂| and |a'₁ ≈A a'₂|, |R a₁ a'₁| implies |R a₂
a'₂|. }%
We formalize the product $\mathcal{A}_{s_1} \times ... \times
\mathcal{A}_{s_n}$ as the setoid of \emph{heterogeneous vectors}. The
type of heterogeneous vectors is parameterized by a set of codes
(sorts) and a family of sets indexed by those codes and indexed over a
list of codes:
\begin{spec}
data HVec {I : Set}  (A : I → Set) : List I → Set where
  ⟨⟩  : HVec A []
  _▹_ : ∀  {i is} → A i → HVec A is → HVec A (i ∷ is)
\end{spec}
\noindent Given |A : I → Set| and |R : (i : I) → Rel (A i)| we let |R
*| be the point-wise extension of |R| over heterogeneous vectors.
This construction is used to define the setoid of heterogeneous
vectors given a family of setoids |A : I → Setoid|; for |is : List I|,
|A ✳ is| refers to the setoid of heterogeneous vectors with index
|is|. The interpretation of an operation $f \colon [s_1,…,s_n]
\Rightarrow s$ should be a setoid morphism |A ✳ [s₁,…,sₙ] ⟶ A s|.

An algebra for a signature $\Sigma$ is a record with two fields: the
interpretation for sorts and the interpretation for operations.
\begin{spec}
record Algebra (Σ : Signature) : Set₁  where
  field
    _⟦_⟧ₛ   : sorts Σ → Setoid
    _⟦_⟧ₒ    : ∀  {ar s} → ops Σ (ar , s) → _⟦_⟧ₛ ✳ ar ⟶ _⟦_⟧ₛ s
\end{spec}
% Me parece que esto no es necesario!
%  _⟦_⟧ₛ* : (ar : Arity Σ) → Set
%  _⟦_⟧ₛ* ar = Carrier (HVecSet (sorts Σ) _⟦_⟧ₛ ar)


Let us see an example of a |Sig₁|-algebra. The sorts |nat| and |bool|
are interpreted by the trivial setoids over |ℕ| and |Bool|, respectively.
\begin{spec}
iS : sorts Sig₁ → Setoid
iS nat   = setoid ℕ
iS bool  = setoid Bool

iO : ∀ {ar s} → ops Sig₁ (ar ↦ s) → (iS ✳ ar) ⟶ iS s
iO (const n)  = record  { _⟨$⟩_ = λ { ⟨⟩ → n } ; cong = ? }
iO plus  = record { _⟨$⟩_ = λ {⟨⟨ n₁ , n₂ ⟩⟩ → n₁ + n₂} ; cong = ? }
iO eq    = record { _⟨$⟩_ = λ {⟨⟨ n₁ , n₂ ⟩⟩ → n₁ =ₙ n₂} ; cong = ? }
iO and   = record { _⟨$⟩_ = λ {⟨⟨ b₁ , b₂ ⟩⟩ → b₁ ∧ b₂} ; cong = ? }
       
Alg₁ : Algebra Sig₁
Alg₁ = record { _⟦_⟧ₛ = iS ; _⟦_⟧ₒ = iO }
\end{spec}

\noindent We omit the proofs that each function preserve the
definitional relation as they are utterly uninteresting (here and
there we use |?| to indicate omitted code). % When one uses Agda
% interactively, the type-checker infers the argument of the
% interpretation of each operation.

\paragraph{Homomorphism} % In this section we fix a signature |Σ: Signature|; in the
% formalization this is achieved with a module with parameters.
Let $\mathcal{A}$ and $\mathcal{B}$ be two $\Sigma$-algebras, a
\emph{homomorphism} $h$ from $\mathcal{A}$ to $\mathcal{B}$ is a
family of functions indexed by the sorts
$h_s : \mathcal{A}_s \rightarrow \mathcal{B}_s$, such that for each
operation $f : [s_1,...,s_n] \Rightarrow s$, the following holds:
\begin{equation}
  h_s(f_{\mathcal{A}}(a_1,...,a_n)) = f_{\mathcal{B}}(h_{s_1}\,a_1,...,h_{s_n}\,a_n)\label{eq:homcond}
\end{equation}
We formalize homomorphisms from an algebra |A| to an algebra |B| as a
family of setoid morphisms indexed over sorts
\begin{spec}
_⟿_ : (A : Algebra Σ) → (B : Algebra Σ) → Set
A ⟿ B = (s : sorts Σ) → (A ⟦ s ⟧ₛ) ⟶ (B ⟦ s ⟧ₛ)
\end{spec}
\noindent and a proof that it satisfies condition \eqref{eq:homcond}, expressed by
\begin{spec}
homCond : A ⟿ B → Set
homCond h = ∀ ar s (f : ar ↦ s) (as : ∥ A ⟦ ar ⟧ₛ* ∥) → 
         h s ⟨$⟩ (A ⟦ f ⟧ₒ ⟨$⟩ as) ≈ₛ B ⟦ f ⟧ₒ ⟨$⟩ map h as
\end{spec}
\noindent where |_≈ₛ_| is the equivalence relation of the setoid
|B ⟦ s ⟧ₛ| and |map h| is the obvious extension of |h| over vectors.
For |H : Homo A B|, the family of setoid morphism is |′ H ′ : A ⟿ B|
and |cond H| is the proof for |homCond ′ H ′|.

As expected, we have |Idₕ A : Homo A A| and |F ∘ₕ G : Homo A C| when
|F : Homo A B| and |G : Homo B C|.  Two homomorphisms |F , F' : Homo A B| are
equal when their corresponding setoid morphisms are extensionally equal:
\begin{spec}
  _≈ₕ_  : ∀ {A B} → Homo A B → Homo A B → Set
  F ≈ₕ F' = (s : sorts Σ) → ′ F ′ s ≈→ ′ F' ′ s
\end{spec}
\noindent Since |_≈→_| is an equivalence relation, |_≈ₕ_| is also of
equivalence. With respect to this equality, it is straightforward to
prove the associativity of the composition |_∘ₕ_| and that |Idₕ| is
the identity for the composition.

\comment{It is straightforward to define the product |A₁ × A₂| of algebras |A₁|
and |A₂| and the projection homomorphisms |Πᵢ : Homo (A₁ × A₂) Aᵢ| where
|′ Πᵢ ′ _ ⟨$⟩ p = projᵢ p|.}

\subsection{Quotient and subalgebras}
In order to prove the more basic results of universal algebra, we need
to formalize subalgebras, congruence relations, and quotients.

\paragraph{Subalgebra}

Usually, a subalgebra $\mathcal{B}$ of an algebra $\mathcal{A}$
consists of a family of subsets $\mathcal{B}_s \subseteq
\mathcal{A}_s$, that are closed by the interpretation of operations;
that is, for every $ f : [s_1, \ldots,s_n] \Rightarrow s$ the following
condition holds
\begin{equation}
(a_1,\ldots,a_n) \in \mathcal{B}_{s_1} \times \cdots \times\mathcal{B}_{s_n}   \text{ implies }
  f_\mathcal{A}(a_1,\ldots,a_n) \in B_{s} \enspace .
 \label{eq:opclosed}
\end{equation} 

As shown by Salvesen and Smith \cite{salvesen-subsets}, subsets cannot be added as a
construction in intensional type-theory because they lack desirable
properties; however, one can represent the subset |{ a ∈ A : P a}| as
the dependent sum |Σ[ a ∈ A ] P| whose inhabitants are pairs |(a , p)|
where |a : A| and |p : P a|. We can lift this construction to setoids:
the carrier of |SubSetoid A P| is |Σ[ a ∈ ∥ A ∥ ] P| and its equivalence
relation is that of |A|.

If |P| is well-defined, then related elements in |A| are either both
or none of them in the subsetoid; this is a natural property to expect
for subalgebras. For |A : Algebra Σ|, a family of predicates |P|
indexed over the sorts satisfies \eqref{eq:opclosed} if
\begin{spec}
    opClosed : ((s : sorts Σ) → Pred (∥ A ⟦ s ⟧ₛ∥)) → Set
    opClosed P = ∀ {ar s} (f : ops Σ (ar , s)) → (P ⇨v ⟨→⟩ P s) (A ⟦ f ⟧ₒ ⟨$⟩_)
\end{spec}
\noindent We denote with |P ⇨v| the point-wise extension of |P| over
vectors; |(Q ⟨→⟩ R) f| can be read as the pre-condition |Q| implies
post-condition |R| after applying |f|. In summary, given a family |P|
of predicates, such that |P s| is well-defined and |P| is |opClosed|
we can define the |SubAlgebra A P|:
\begin{spec}
SubAlgebra : ∀ {Σ} A P → WellDef P → opClosed P → Algebra Σ
SubAlgebra A P _ opC = record   { _⟦_⟧ₛ s = SubSetoid (A ⟦ s ⟧ₛ) (Pₛ s) 
                               ; _⟦_⟧ₒ f = record { _⟨$⟩_ = io  ; cong = ? } }
    where  io : ∀ {ar s} → (f : ops Σ (ar , s)) → _
           io f as = A ⟦ f ⟧ₒ ⟨$⟩ map (λ _ → proj₁) as , opC f (⇨₂ as)
\end{spec}
\noindent We interpret operations as in the original algebra over the first
components of the vector |as|; to show that the results
satisfies |P s|, we can apply |opC f| to |⇨₂ as : P ⇨v map (λ_ → proj₁) as|.

\paragraph{Congruence and Quotients}
A \emph{congruence} on a $\Sigma$-algebra $\mathcal{A}$ is a family
$Q$ of equivalence relations indexed by sorts closed by the operations
of the algebra. This condition is called \emph{substitutivity} and can
be formalized using the point-wise extension of $Q$ over vectors: for
every operation $ f : [s_1, \ldots,s_n] \Rightarrow s$
\begin{equation}
  (\vec{a},\vec{b}) \in Q_{s_1} \times \cdots \times Q_{s_n} \text{ implies }
 (f_{\mathcal{A}}(\vec{a}) , f_{\mathcal{A}}(\vec{b})) \in Q_s\label{eq:congcond}
\end{equation} 
\comment{\noindent Let us remark that this condition could be defined as
\eqref{eq:opclosed} taking $Q$ as a predicate over $\mathcal{A} \times
\mathcal{A}$.}

Remember that a binary relation over a setoid is well-defined if it is
preserved by the setoid equality; this notion can be extended over
families of relations in the obvious way. In our formalization, a
congruence on an algebra |A| is a family |Q| of well-defined,
equivalence relations. The substitutivity condition
\eqref{eq:congcond} is aptly captured by the generalized containment
operator |_=[_]⇒_| of the standard library, where |P =[ f ]⇒ Q| if,
for all |a,b ∈ A|, |(a,b) ∈ P| implies |(f a, f b) ∈ Q|.

\begin{spec}
record Congruence (A : Algebra Σ) : Set where
  field
    rel : (s : sorts Σ) → Rel (Carrier (A ⟦ s ⟧ₛ))
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
the three isomorphims theorems. Although there is some small overhead
by the coding of subalgebras, the proofs are almost the same as in
informal mathematics. For proving these results we also defined the
\emph{kernel} and the \emph{homomorphic} image of homomorphisms.

\begin{theorem}[First isomorphism theorem] If $h : \alg{A} \rightarrow \alg{B}$
is an epimorphism, then $\alg{A} / \mathop{ker} h \simeq \alg{B}$.
\end{theorem}

\begin{theorem}[Second isomorphism theorem] Let $\phi,\psi$ be congruences over $\alg A$,
such that $\psi \subseteq \phi$, then $(\alg A / \phi) \simeq \alg A / (\phi / \psi)$.
\end{theorem}

\begin{theorem}[Third isomorphism theorem] Let $\alg B$ is a
subalgebra of $\alg A$ and $\phi$ is a congruence over $\alg A$. Let
$[\alg B]^{\phi}=\{K \in A / \phi : K \cap B \not= \emptyset\}$ and
let $\phi_B$ be the restriction of $\phi$ to $\alg B$, then
\begin{enumerate*}[label=(\roman*),itemjoin={}]
\item $\phi_B$ is a congruence over $\alg B$;
\item $[\alg B]^{\phi}$ is a subalgebra of $\alg A$; and
\item $[\alg B]^{\phi} \simeq \alg B / \phi_B$.
\end{enumerate*}
\end{theorem}

\subsection{Term algebra is initial}

A $\Sigma$-algebra $\mathcal{A}$ is called \emph{initial} if for any
$\Sigma$-algebra $\mathcal{B}$ there exists exactly one homomorphism
from $\mathcal{A}$ to $\mathcal{B}$. We give an abstract definition of
this universal property, existence of an unique element, for any set
|A| and any relation |R|
\begin{spec}
hasUnique {A} _≈_ = A × (∀ a a' → a ≈ a')
\end{spec}
\comment{Obviously, if a set has a unique element, then the relation
is an equivalence. Alternatively one can asks for a witness |a:A| and
a proof of |(a':A) → a ≈ a'|; in this case one should also asks the
relation to be of equivalence.}
\noindent and initiality can be formalized directly as the predicate
that the algebra has a unique homomorphism to any other algebra:
\begin{spec}
Initial : ∀ {Σ} → Algebra Σ → Set
Initial {Σ} A = ∀ (B : Algebra Σ) → hasUnique (_≈ₕ_ A B)
\end{spec}

Given a signature $\Sigma$ we can define the \emph{term algebra}
$\mathcal{T}$, whose carriers are sets of well-typed words built up
from the function symbols.  Sometimes this universe is called the
\emph{Herbrand Universe}  and is inductively defined:
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
    term : ∀  {ar s} → (f : ops Σ (ar ↦ s)) → (HVec HU ar) → HU s
\end{spec}

\noindent We use propositional equality to turn each
$\mathcal{T}_s$ into a
setoid, thus completing the interpretation of sorts. To interpret
an operation $f \colon [s_1,\ldots,s_n] \Rightarrow s$ we map the
tuple $⟨t_1,\ldots,t_n⟩$ to the term
$f(t_1,\ldots,t_n)$ in $\mathcal{T}_s$; we omit the proof
of |cong|.
\begin{spec}
  T : (Σ : Signature) Algebra Σ
  T Σ = record  { _⟦_⟧ₛ = setoid ∘ (HU {Σ}) ; _⟦_⟧ₒ  = ∣_|ₒ }
    where | f ∣ₒ = record { _⟨$⟩_ = term f ; cong = ? }
\end{spec}

\noindent Recursively interpreting terms yields an homomorphism
$h_A \colon \mathcal{T} \to \mathcal{A}$ defined by
\[
  h_A (f(t_1,\ldots,t_n)) = f_{\mathcal{A}}\,(h_A\,t_1,...,h_A\,t_n) \enspace .
\] 
\noindent We cannot translate this definition directly in Agda, instead
we have to mutually define | ∣h∣→A | and its extension over vectors
| ∣h*∣→A A {ar} : Vec HU ar → A ⟦ ar ⟧ₛ*|
\begin{spec}
  ∣h∣→A : (A : Algebra Σ) → {s : sorts Σ} → HU s → ∥ A ⟦ s ⟧ₛ ∥
  ∣h∣→A A (term f ts) = A ⟦ f ⟧ₒ ⟨$⟩ (∣h*∣→A ts)
\end{spec}
\noindent It is straightforward to prove that |∣h∣→A| preserves
propositional equality and satisfies the homomorphism condition by
construction; thus we know that there is a homomorphism | ∣h∣A : (A :
Algebra Σ) → Homo (T Σ) A|; to finish the proof that | T Σ | is
initial, we prove, by recursion on the structure of terms,that any
pair of homomorphism are equal.
%\begin{spec}
%|h|A  : (A : Algebra Σ) → Homo |T| A
%|h|A A = record  { ′_′  =  λ s → record {_⟨$⟩_ = ∣h∣→A A {s} ; cong  = {!!}}
%                 ; cond = {!!}}
%\end{spec}
%
%\noindent We let | ∣h∣A |
%\begin{spec}
%  |T|isInitial : Initial ∣T∣
%  |T|isInitial A = ∣h∣→A A , ?
%\end{spec}

