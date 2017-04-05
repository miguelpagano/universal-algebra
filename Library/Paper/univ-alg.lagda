\section{Universal Algebra}
\label{sec:univ-alg}

In this section we present our formalization in Agda of the core
concepts of heterogenouos universal algebra, up to the three
isomorphism theorems and initiality of the term algebra.  As far as we
know, there are two formalizations of (multisorted) universal algebra
in type-theory: Capretta's implementation in Coq and the formalization
of allegories in Agda by \citet{kahl-2011}. 

Our reference for heterogeneous universal algebra is
\citet{meinke-tucker-1992}. We will recall some of the standard
definitions in order to explain the most salient aspects of our
formalization, and its more bureaucratic and less interesting parts
will be omitted. The complete development is available at
\url{https://cs.famaf.unc.edu.ar/~mpagano/univ-alg/}.

\subsection{Signature, algebra and homomorphism}

\paragraph{Signature.}

A \emph{signature} is a pair of sets $(S,F)$, called \textit{sorts}
and \textit{operations} (or \textit{function symbols})
respectively. An operation is a triple $(f,[s_1,\ldots,s_n],s)$
consisting of a \textit{name}, a list of sorts (its \textit{arity)},
and another sort (its \textit{target sort}). We write operations as a
type declaration $f : [s_1,...,s_n] \Rightarrow s$ and say ``$f$ has
type $[s_1,...,s_n] \Rightarrow s$''.

We prefer to think of operations as a family of sets indexed by
types. Thus, we represent signatures in Agda by a record with fields
|sorts|, which is a Set, and |ops|, which is a family of sets indexed
by the types of operations:

\begin{spec}
record Signature : Set₁ where
  field
    sorts  : Set
    ops  : List sorts × sorts → Set 

  Arity : Set
  Arity = List sorts
\end{spec}

\noindent
This way of defining the set of operations admits of having an
infinite number of sorts and operations, contrasting with Capretta's
formalization where both the set of sorts and operations are
finite. More important, we can define functions or predicates over
operations of a given type.
\manu{pensar en por qué es una ventaja
  tener infinitos sorts y operaciones. Y encontrar algún predicado o
  función interesante.}

As an example, consider the signature for arithmetic and boolean
expressions; we introduce operations with the same type in the
same line.
\begin{spec}
data S : Set where nat : S ; bool : S 

data O : (List S) × S → Set where
  const       :  ℕ → O ([] , nat)
  eq          :  O ([ nat , nat ] , bool)
  and         :  O ([ bool , bool ] , bool)
  plus        :  O ([ nat , nat ] , nat)

Sig₁ : Signature
Sig₁ = record { sorts = S ; ops = O }
\end{spec}

\noindent Notice that there is a constant operation |const n| for each
natural number |n|, thus permitting a straightforward encoding of
numbers as terminals of the abstract grammar of expressions.
% ¿adelantar que frases de la gramática abstracta son las expresiones?
Let us illustrate the possibility of proving properties of operations
according to their types by showing that operations with target sort
|nat| are monosorted:
\begin{spec}
data monoSorted {ar s} : ops (ar ↦ s) → Set where
   isMono : (o : ops (ar ↦ s)) → All (_≡_ s) ar → monoSorted o  

monoNat : ∀ {ar} → (o : O (ar  ↦ nat)) → monoSorted o
monoNat (const n) = isMono (const n) []
monoNat plus = isMono plus (_≡_.refl ∷ _≡_.refl ∷ [])
\end{spec}
There are only two cases in |monoNat| because the other
constructors of |O| have target sort |bool|.

\paragraph{Algebra.}

Usually, an \emph{algebra} $\mathcal{A}$ for the signature $\Sigma$,
or a $\Sigma$-algebra, consists of a family of sets indexed by the
sorts of $\Sigma$ and a family of functions indexed by the operations
of $\Sigma$. We use $\mathcal{A}_s$ for the \emph{interpretation} or
the \emph{carrier} of the sort $s$; given an operation
$f \colon [s_1,...,s_n] \Rightarrow s$, the interpretation of $f$ is a
total function
$f_{\mathcal{A}}\colon \mathcal{A}_{s_1} \times ... \times
\mathcal{A}_{s_n} \rightarrow \mathcal{A}_s$. What this definitions
hides is that carriers are pairs of a set and its equality; in
type-theory one makes this structure apparent by using Bishop's sets
(\ie sets paired with an equivalence relation) as the interpretation
of sorts. In type-theory Bishop's sets are better known as setoids and
they were thoroughly studied by \citet{barthe-setoids-2003}; in the
following, we introduce the defintion of setoids in Agda and some
constructions around them.

Setoids are defined in the the standard library
\cite{danielsson-agdalib} of Agda, which we conveniently use as far as
possible, as a record with fields: the |Carrier : Set|, the relation
|_≈_ : Rel Carrier|, and the proof that |IsEquivalence _≈_|. The
operator | ∥_∥ | represents the forgetful functor from setoids to
sets, so that | ∥ (A,_≈A_,_) ∥ = A|.\manu{Miguel pregunta si conviene
notar que en Agda no hay coerciones} There is an obvios
functor |setoid : Set → Setoid| which maps a type |A| to the setoid
defined by the propositional equality over that type. In the standard
library it is also defined the point-wise extension of two setoids
|A ×-setoid B|.

Once sorts are interpreted as setoids, operations should be
interpreted as setoid morphisms; \ie functions which preserve the
equivalence relation.  Given two setoids |Ȧ := (A,_≈A_,p)| and |Ḃ :=
(B,_≈B_,q)|, the inhabitants of |Ȧ ⟶ Ḃ| are morphism from |Ȧ| to |Ḃ|
records with fields
|_⟨$⟩_ : A → B| and |cong : ∀ a a' → a ≈A a' → _⟨$⟩_ a ≈B
_⟨$⟩_ a'|. Similarly, predicates over setoids should
be even over equal elements; thus we set
\begin{spec}
  WellDef : ∀ {ℓ₁ ℓ₂ ℓ₃} → (A : Setoid ℓ₁ ℓ₂) → Pred (∥ A ∥) ℓ₃ → Set _
  WellDef A P = ∀ {a a'} → a ≈A a' → P a → P a'
\end{spec}
\noindent If |P| is well-defined, we deduce |P a ↔ P a'| if |a ≈
a'|, because equality is symmetric. Notice also that we can
define that a relation is well-defined using the product of 
setoids:
\begin{spec}
  WellDefBin : ∀ {ℓ₁ ℓ₂ ℓ₃} → (A : Setoid ℓ₁ ℓ₂) → Rel (∥ A ∥) ℓ₃ → Set _
  WellDefBin A R = WellDef (A ×-setoid A) (λ {(a , b) → R a b}) 
\end{spec}
\noindent Expanding this definition we discover that |WellDefBin A R|
iff for all |a₁ ≈A a₂| and |a'₁ ≈A a'₂|, |R a₁ a'₁| implies |R a₂
a'₂|. 

We formalize the product $\mathcal{A}_{s_1} \times ... \times
\mathcal{A}_{s_n}$ as the setoid of \emph{heterogeneous vectors}. The
type of heterogeneous vectors is parameterized by a set of codes
(sorts) and a family of sets indexed by those codes and indexed over a
list of codes:
\begin{spec}
data HVec {ℓ} {I : Set}  (A : I → Set ℓ) : List I → Set ℓ where
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
record Algebra {ℓ₁ ℓ₂}  (Σ : Signature) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    _⟦_⟧ₛ   : sorts Σ → Setoid ℓ₁ ℓ₂
    _⟦_⟧ₒ    : ∀  {ar s} → ops Σ (ar , s) → _⟦_⟧ₛ ✳ ar ⟶ _⟦_⟧ₛ s
\end{spec}
% Me parece que esto no es necesario!
%  _⟦_⟧ₛ* : (ar : Arity Σ) → Set _
%  _⟦_⟧ₛ* ar = Carrier (HVecSet (sorts Σ) _⟦_⟧ₛ ar)


Let us see an example of a |Sig₁|-algebra. The sorts |nat| and |bool|
are interpreted by the trivial setoids over |ℕ| and |Bool|, respectively.
\begin{spec}
iS : sorts Sig₁ → Setoid _ _
iS nat   = setoid ℕ
iS bool  = setoid Bool

iO : ∀ {ar s} → ops Sig₁ (ar ↦ s) → (iS ✳ ar) ⟶ iS s
iO (const n)  = record  { _⟨$⟩_ = λ { ⟨⟩ → n } ; cong = {! !} }
iO plus  = record { _⟨$⟩_ = λ {⟨⟨ n₁ , n₂ ⟩⟩ → n₁ + n₂} ; cong = {! !} }
iO eq    = record { _⟨$⟩_ = λ {⟨⟨ n₁ , n₂ ⟩⟩ → n₁ =ₙ n₂} ; cong = {! !} }
iO and   = record { _⟨$⟩_ = λ {⟨⟨ b₁ , b₂ ⟩⟩ → b₁ ∧ b₂} ; cong = {! !} }
       
Alg₁ : Algebra Sig₁
Alg₁ = record { _⟦_⟧ₛ = iS ; _⟦_⟧ₒ = iO }
\end{spec}

\noindent We omit the proofs that each function preserve the
definitional relation as they are utterly uninteresting (here and
there we use |{! !}| to indicate omitted code). When one uses Agda
interactively, the type-checker infers the argument of the
interpretation of each operation.

\paragraph{Homomorphism} % In this section we fix a signature |Σ: Signature|; in the
% formalization this is achieved with a module with parameters.
Let $\mathcal{A}$ and $\mathcal{B}$ be two $\Sigma$-algebras, a \emph{homomorphism}
$h$ from $\mathcal{A}$ to $\mathcal{B}$ is a family of functions indexed by the
sorts $h_s : \mathcal{A}_s \rightarrow \mathcal{B}_s$,
such that for each operation $f : [s_1,...,s_n] \Rightarrow s$, the following holds:
\begin{equation}
  h_s(f_{\mathcal{A}}(a_1,...,a_n)) = f_{\mathcal{B}}(h_{s_1}\,a_1,...,h_{s_n}\,a_n)\label{eq:homcond}
\end{equation}

We formalize homomorphisms from an algebra |A| to an algebra |B| as a
family of functions indexed over sorts
\begin{spec}
_⟿_ : (A : Algebra Σ) → (B : Algebra Σ) → Set _
A ⟿ B = (s : sorts Σ) → (A ⟦ s ⟧ₛ) ⟶ (B ⟦ s ⟧ₛ)
\end{spec}
and a proof that it satisfies condition \eqref{eq:homcond}, expressed by
\begin{spec}
homCond : ∀ ty → A ⟿ B → ops Σ ty → Set _
homCond (ar ↦ s) h f =   (as : ∥ A ⟦ ar ⟧ₛ* ∥) → 
         h s ⟨$⟩ (A ⟦ f ⟧ₒ ⟨$⟩ as) ≈ₛ B ⟦ f ⟧ₒ ⟨$⟩ map h as
\end{spec}
\noindent where |_≈ₛ_| is the equivalence relation of the setoid
|B ⟦ s ⟧ₛ| and |map h| is the obvious extension of |h| over vectors.

For |H : Homo A B|, the family of setoid morphism is |′ H ′ : A ⟿ B|
and |cond H| is the proof for |homCond ′ H ′|; and for |a : A ⟦ s ⟧ₛ|, we
have |′ H ′ s ⟨$⟩ a : B ⟦ s ⟧ₛ|.

\subsection{Quotient and subalgebras}
In order to prove the more basic results of universal algebra, we need
to formalize subalgebras, congruence relations, and quotients.

\paragraph{Subalgebra}

Usually, a subalgebra $\mathcal{B}$ of an algebra $\mathcal{A}$
consists of a family of subsets $\mathcal{B}_s \subseteq
\mathcal{A}_s$, that are closed by the interpretation of operations;
that is, for every $ f : [s_1, \ldots,s_n] \Rightarrow s$ the following
condition holds
This condition is called \emph{substitutivity} and can
be formalized using the point-wise extension of $Q$ over vectors: for
every operation $ f : [s_1, \ldots,s_n] \Rightarrow s$
\begin{equation}
(a_1,\ldots,a_n) \in \mathcal{B}_{s_1} \times \cdots \times\mathcal{B}_{s_n}   \text{ implies }
  f_\mathcal{A}(a_1,\ldots,a_n) \in B_{s} \enspace .
 \label{eq:opclosed}
\end{equation} 

As shown by \citet{salvesen-subsets}, subsets cannot be added as a
construction in intensional type-theory because they lack desirable
properties; however, one can represent the subset |{ a ∈ A : P a}| as
the dependent sum |Σ[ a ∈ A ] P| whose inhabitants are pairs |(a , p)|
where |a : A| and |p : P a|. We can lift this construction to setoids:
the carrier of |SubSetoid A P| is |Σ[ a ∈ ∥ A ∥ ] P| and we take the
equality over the first projections, this clearly yields an
equivalence relation.

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
  SubAlgebra A P _ opC = record  {
        _⟦_⟧ₛ s = SubSetoid (A ⟦ s ⟧ₛ) (Pₛ s) 
  ;     _⟦_⟧ₒ f = record { _⟨$⟩_ = if  ; cong = ? } }
    where  if : ∀ {ar s} → (f : ops Σ (ar , s)) → _
           if f vs = A ⟦ f ⟧ₒ ⟨$⟩ map (λ _ → proj₁) vs , opC f (⇨₂ vs)
\end{spec}
\noindent We interpret operations as in the original algebra over the first
components of the vector |vs|; to show that the results
satisfies |P s|, we can apply |opC f| to |⇨₂ vs : P ⇨v map (λ_ → proj₁) as|.

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
\noindent Let us remark that this condition could be defined as
\eqref{eq:opclosed} taking $Q$ as a predicate over $\mathcal{A} \times
\mathcal{A}$.

Remember that a binary relation over a setoid is well-defined if it is
preserved by the setoid equality; this notion can be extended over
families of relations in the obvious way. In our formalization, a
congruence on an algebra |A| is a family |Q| of well-defined,
equivalence relations. The substitutivity condition
\eqref{eq:congcond} is aptly captured by the generalized containment
operator |_=[_]⇒_| of the standard library, where |P =[ f ]⇒ Q| if,
for all |a,b ∈ A|, |(a,b) ∈ P| implies |(f a, f b) ∈ Q|.

\begin{spec}
record Congruence (A : Algebra Σ) : Set _ where
  field
    rel : (s : sorts Σ) → Rel (Carrier (A ⟦ s ⟧ₛ)) _
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
from |A| and use |Q s| as the equivalence relation over |∥ A ⟦ s ⟧ₛ ∥|;
operations are interpreted just as in |A|; operations are 
interpreted as before and the congruence proof is given by |csubst Q|.


\subsection{Term algebra is initial}
\manu{Comentar más lo simple que sale respecto a lo que tiene Capretta.}
\paragraph{Initial algebra.}
A $\Sigma$-algebra $\mathcal{A}$ is called \emph{initial} if for all
$\Sigma$-algebra $\mathcal{B}$ there exists exactly one homomorphism
from $\mathcal{A}$ to $\mathcal{B}$, i. e., if we have two
homomorphisms from $\mathcal{A}$ to $\mathcal{B}$, then they are equals.

We can define the notion of \textit{uniqueness} respects to an
equivalence relation:

\begin{spec}
Unique : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} →  (_≈_ : Rel A ℓ₂) →
                                   IsEquivalence _≈_ → Set _
Unique {A = A} _≈_ _ = A × (∀ a a' → a ≈ a')
\end{spec}


The appropiate notion of equality between homomorphisms is the
extensional equality respects to the equivalence relation of the
respectives setoids of each algebra.
If |S₁| and |S₂| are setoids, and |≈S₂| is the equivalence relation of
|S₂|, we define extensional equality:

\begin{spec}
  _≈→_ : Rel (S₁ ⟶ S₂) _
  f ≈→ g  = ∀ (a : ∥ S₁ ∥) → (f ⟨$⟩ a) ≈S₂ (g ⟨$⟩ a)
\end{spec}

\noindent It's easy to prove that this relation is of equivalence.
Call |≈ₕequiv| to this proof.

Two homomorphisms |H G : Homo A B| are equals if for every sort |s|,
its corresponding setoid morphisms are extensionally equal, that is
|′ H ′ s ≈→ ′ G ′ s|:

\begin{spec}
  _≈ₕ_  : ∀ A B → (H G : Homo A B) → Set _
  H ≈ₕ G = (s : sorts Σ) → ′ H ′ s ≈→ ′ G ′ s
\end{spec}

We define the initial algebra of a signature |Σ| with a record with
two elements: An algebra |alg| and the proof of uniqueness of the
homomorphism between |alg| and any other:

\begin{spec}
record Initial  : Set _ where
  field
    alg   :  Algebra Σ
    init  :  (A : Algebra Σ) → Unique (_≈ₕ_ alg A) ≈ₕequiv
\end{spec}

\paragraph{Term algebra.}

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

\begin{spec}
  data HU : (s : sorts Σ) → Set where
    term : ∀  {ar s} → (f : ops Σ (ar ↦ s)) → (HVec HU ar) → HU s
\end{spec}

\noindent We use propositional equality to turn each
$\mathcal{T}_s$ in a
setoid, thus completing the interpretation of sorts. To interpret
an operation $f \colon [s_1,\ldots,s_n] \Rightarrow s$ we map the
tuple $⟨t_1,\ldots,t_n⟩$ to the term
$f(t_1,\ldots,t_n)$ in $\mathcal{T}_s$; we omit the proof
of |cong|.
\begin{spec}
  |T| : Algebra Σ
  |T| = (setoid ∘ HU) ∥ (λ f → record  { _⟨$⟩_ = term f ; cong = {!!}})
\end{spec}

\noindent Now we turn to prove that the term algebra is initial; so for any
$\Sigma$-algebra $\mathcal{A}$ we define the homomorphism $h_A \colon
\mathcal{T} \to \mathcal{A}$ \[
  h_A (f(t_1,\ldots,t_n)) = f_{\mathcal{A}}\,(h_A\,t_1,...,h_A\,t_n) \enspace .
\] 
\noindent We can define in Agda this homomorphism in a way similar to
this\footnote{Indead, because of the Agda termination checker, we must
define two mutually recursive functions, one
mappings terms to elements of $\mathcal{A}$ and the other mapping
vectors of terms to vectors of $\mathcal{A}$}:
\begin{spec}
  ∣h∣→A : ∀ {s : sorts Σ} → HU s → ∥ A ⟦ s ⟧ₛ ∥
  ∣h∣→A (term f ts) = A ⟦ f ⟧ₒ ⟨$⟩ (map ∣h∣→A ts)
\end{spec}
 
With the function |∣h∣→A| we can define the homomorphism. The proofs of
|cong| and the homomorphism condition are straightforward,
we omit them.

\begin{spec}
|h|A : (A : Algebra Σ) → Homo |T| A
|h|A = record  { ′_′  =  λ s → record 
                         {_⟨$⟩_ = ∣h∣→A {s}
                         ; cong  = {!!}}
               ; cond = {!!}}
\end{spec}

With this homomorphism we can define the proof of initiality of the
term algebra. We omit the proof of uniqueness because presents no
interesting difficulties.

\begin{spec}
  |T|isInitial : Initial
  |T|isInitial = record  { alg = |T|
                         ; init = λ A → |h|A , {! !} }
\end{spec}

      
\subsection{Theorems}

We conclude this section with the proof of some theorems.
