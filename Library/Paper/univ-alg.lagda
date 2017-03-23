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
  and or      :  O ([ bool , bool ] , bool)
  plus prod   :  O ([ nat , nat ] , nat)

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
data monoSorted {ar s} : ops (ar , s) → Set where
   isMono : (o : ops (ar , s)) → All (_≡_ s) ar → monoSorted o  

monoNat : ∀ {ar} → (o : O (ar , nat)) → monoSorted o
monoNat (const n) = isMono (const n) []
monoNat plus = isMono plus (_≡_.refl ∷ _≡_.refl ∷ [])
monoNat prod = isMono prod (_≡_.refl ∷ _≡_.refl ∷ [])
\end{spec}
There are only three cases in |monoNat| because the other
constructors of |O| have target sort |bool|.

\paragraph{Algebra.}

Usually, an \emph{algebra} $\mathcal{A}$ of a signature $\Sigma$, or a
$\Sigma$-algebra, consists of a family of sets indexed by the sorts of
$\Sigma$ and a family of functions indexed by the operations of
$\Sigma$. We use $\mathcal{A}_s$ for the \emph{interpretation} or the
\emph{carrier} of the sort $s$; given an operation $f \colon
[s_1,...,s_n] \Rightarrow s$, the interpretation of $f$ is a total
function $f_{\mathcal{A}}\colon \mathcal{A}_{s_1} \times ... \times
\mathcal{A}_{s_n} \rightarrow \mathcal{A}_s$. It is assumed that
every carrier comes equipped with a notion of equality and several
theorems refer to that equality.

In type-theory, however, it is well-known that one can equip a type
with several notions of equality (a relevant example for this paper is
the carrier of well-formed terms of a given signature: for the initial
algebra one takes the definitional equality, but for proving
completeness of equational logic one equates terms whenever they are
provable equal under the corresponding axioms). The well-known
solution is to represent carriers as setoids; \ie as types paired
with an equivalence relation.

Setoids are defined in the the standard library
\cite{danielsson-agdalib} of Agda, we conveniently use it as far as
possible, as a record with fields: the |Carrier : Set|, the relation
|_≈_ : Rel Carrier|, and the proof that |IsEquivalence _≈_|.  The
operator | ∥_∥ | represents the forgetful functor from setoids to
sets, so that | ∥ (A,_≈A_,_) ∥ = A|.

Once sorts are interpreted as setoids, operations should be
interpreted as setoid morphisms; \ie functions which preserve the
equivalence relation.  Given two setoids |Ȧ := (A,_≈A_,_)| and |Ḃ :=
(B,_≈B_,_)|, the inhabitants of |Ȧ ⟶ Ḃ| are 
morphism from |Ȧ| to |Ḃ| defined by records with fields |_⟨$⟩_ : A → B|
and |cong : ∀ a a' → a ≈A a' → f ⟨$⟩ a ≈B f ⟨$⟩ a'|.

We formalize the product $\mathcal{A}_{s_1} \times ... \times
\mathcal{A}_{s_n}$ as the setoid of \emph{heterogeneous vectors}. The
type of heterogeneous vectors is parameterized by a set of codes
(sorts) and a family of sets indexed by those codes and indexed over a
list of codes:
\begin{spec}
data HVec {ℓ} {I : Set}  (A : I -> Set ℓ) : List I → Set ℓ where
  ⟨⟩  : HVec A []
  _▹_ : ∀  {i is} → A i → HVec A is → HVec A (i ∷ is)
\end{spec}
\noindent When |A| is a family of setoids |I → Setoid|, and |is : List I|, it is
straightforward to promote this construction to setoids (the
equivalence relation is defined point-wisely); we use |A ✳ is| to
refer to the setoid of heterogeneous vectors indexed in |is|. The
interpretation of an operation $f \colon [s_1,…,s_n] \Rightarrow s$
should be a setoid morphism |A ✳ [s₁,…,sₙ] ⟶ A s|.


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


Let us see an example of a |Sig₁|-algebra. We interpret sorts |nat| and
|bool| with setoids |ℕ| and |Bool|, where the equivalence relation
is the definitional equality of Agda (the function |setoid| constructs
this trivial setoid).

\begin{spec}
iS : sorts Sig₁ → Setoid _ _
iS nat   = setoid ℕ
iS bool  = setoid Bool

iO : ∀ {ar s} → ops Sig₁ (ar ↦ s) → (iS ✳ ar) ⟶ iS s
iO (const n)  = record  { _⟨$⟩_ = λ { ⟨⟩ → n } ; cong = {! !} }
iO plus  = record { _⟨$⟩_ = λ {⟨⟨ n₁ , n₂ ⟩⟩ → n₁ + n₂} ; cong = {! !} }
iO prod  = record { _⟨$⟩_ = λ {⟨⟨ n₁ , n₂ ⟩⟩ → n₁ * n₂} ; cong = {! !} }
iO eq    = record { _⟨$⟩_ = λ {⟨⟨ n₁ , n₂ ⟩⟩ → n₁ =ₙ n₂} ; cong = {! !} }
iO and   = record { _⟨$⟩_ = λ {⟨⟨ b₁ , b₂ ⟩⟩ → b₁ ∧ b₂} ; cong = {! !} }
iO or    = record { _⟨$⟩_ = λ {⟨⟨ b₁ , b₂ ⟩⟩ → b₁ ∨ b₂} ; cong = {! !} }
       
Alg₁ : Algebra Sig₁
Alg₁ = record { _⟦_⟧ₛ = iS , _⟦_⟧ₒ = iO }
\end{spec}

\noindent We omit the proofs that each function preserve the
definitional relation as they are utterly uninteresting (here and
there we use |{! !}| to indicate omitted code). When one uses Agda
interactively, the type-checker infers the argument of the
interpretation of each operation.

\paragraph{Homomorphism.}
In this section we fix a signature |Σ: Signature|; in the
formalization this is achieved with a module with parameters.
Let $\mathcal{A}$ and $\mathcal{B}$ be two $\Sigma$-algebras, a \emph{homomorphism}
$h$ from $\mathcal{A}$ to $\mathcal{B}$ is a family of functions indexed by the
sorts $h_s : \mathcal{A}_s \rightarrow \mathcal{B}_s$,
such that for each operation $f : [s_1,...,s_n] \Rightarrow s$, the following holds:
\begin{equation}
  h_s(f_{\mathcal{A}}(a_1,...,a_n)) = f_{\mathcal{B}}(h_{s_1}\,a_1,...,h_{s_n}\,a_n)\label{eq:homcond}
\end{equation}

We formalize homomorphisms from an algebra |A| to an algebra |B| in
a signature |Σ|, as a record with the family of functions
and a proof that it satisfies condition \eqref{eq:homcond}.
We define a family of functions indexed by sorts, from algebra |A|
to algebra |B|:

\begin{spec}
_⟿_ : (A : Algebra Σ) → (B : Algebra Σ) → Set _
A ⟿ B = (s : sorts Σ) → (A ⟦ s ⟧ₛ) ⟶ (B ⟦ s ⟧ₛ)
\end{spec}

An element |h : A ⟿ B| will be a family of setoid morphisms between
the interpretation of each sort in the source and target algebras.
The condition \eqref{eq:homcond} is encoded through a mapping over
the heterogeneous vector |as : A ⟦ ar ⟧ₛ*|, with the function |map⟿|:

\begin{spec}
homCond : ∀ ty → A ⟿ B → ops Σ ty → Set _
homCond  (ar ⇒ s) h f = (as : ∥ A ⟦ ar ⟧ₛ* ∥) →
         h s ⟨$⟩ (A ⟦ f ⟧ₒ ⟨$⟩ as) ≈ₛ B ⟦ f ⟧ₒ ⟨$⟩ map⟿ h as
\end{spec}

\noindent where |_≈ₛ_| is the equivalence relation in the corresponding
setoid.

For |H : Homo A B|, the setoid morphism is |′ H ′ : A ⟿ B| and
|cond H| is the proof that |′ H ′| satisfies \eqref{eq:homcond}:

\begin{spec}
record Homo : (A : Algebra Σ) → (B : Algebra Σ) → Set _ where
  field
    ′_′  : A ⟿ B
    cond : ∀ {ty} (f : ops Σ ty) → homCond ty ′_′ f
\end{spec}

\subsection{Quotient and subalgebras}

\paragraph{Congruence.}

Let $\mathcal{A}$ a $\Sigma$-algebra. A \emph{congruence} is a family
$Q$ of equivalence relations indexed by each sort $s$ of $\Sigma$
on $\mathcal{A}_{s}$,
such that for each operation $f : [s_1,...,s_n] \Rightarrow s$, each
$a_i,b_i \in A_{s_i}$ with $(a_i,b_i) \in Q_{s_i}$ ($1 \leq i \leq n$),
the following holds (this property is usually called ``substitutivity
condition''):

\begin{equation}
  (f_{\mathcal{A}}(a_1,...,a_n) , f_{\mathcal{A}}(b_1,...,b_n)) \in Q_s\label{eq:congcond}
\end{equation}


As we have defined algebras with setoids, each relation $Q_s$ must
preserve the setoid equality. This is formalized in this way:

\begin{spec}
WellDef : _
WellDef = ∀  {s} {x₁ x₂ y₁ y₂ : Carrier (A ⟦ s ⟧ₛ)} →
             (Q : (s : sorts Σ) → Rel (Carrier (A ⟦ s ⟧ₛ))) →
             x₁ ≈ₛ x₂ → y₁ ≈ₛ y₂ → Q s x₁ y₁ → Q s x₂ y₂
\end{spec}

We formalize congruence of an algebra |A| with a record with four
fields: a familiy of binary relations |rel| indexed by sorts, the proof
|cequiv| of that relations are of equivalence, the ``well-defined''
property |welldef|, and the substitutivity condition
\eqref{eq:congcond}. This condition is encoded using the pointwise
extension of a relation in a vector |_∼v_|. If we have two vectors related
by |rel| and we apply the function |A ⟦ f ⟧ₒ| on each one, the results
are related by rel. The function |_=[_]⇒_|, defined in standard
library, expresses exactly this.

\begin{spec}
record Congruence (A : Algebra Σ) : Set _ where
  field
    rel : (s : sorts Σ) → Rel (Carrier (A ⟦ s ⟧ₛ)) _
    welldef : WellDef rel
    cequiv : (s : sorts Σ) → IsEquivalence (rel s)
    csubst : ∀ {ar} {s} → (f : ops Σ (ar , s)) → 
              _∼v_ {R = rel} {is = ar}  =[ _⟨$⟩_ (A ⟦ f ⟧ₒ) ]⇒ rel s
\end{spec}


\paragraph{Quotient}

Let $\mathcal{A}$ a $\Sigma$-algebra and $Q$ a congruence on
$\mathcal{A}$. The \emph{quotient algebra} of $\mathcal{A}$ by $Q$ is
the $\Sigma$-algebra defined by the equivalence classes of $Q$. 
Having implemented the interpretations of sorts with setoids, defining
quotient algebra is trivial, we just replace the equality of each
carrier by the relation of the congruence.

\paragraph{Subalgebra}

In classic logic, a subalgebra consists simply of a subset of the
carrier of each sort closed by the interpretation of operations.
In type theory is more complicated, because the notion of subset
is not the same. Particullary in Agda we don't have subtypes.
We implement subsetoids in the same way than Capretta. An element
in a subsetoid of $S$ is a pair consisting of an element $e \in S$ and
the proof that $e$ satisfies a predicate. The equality of the subsetoid
is the same than $S$, ignoring the second component of each element:

\begin{spec}
record SetoidPredicate (S : Setoid _ _) : Set _  where
  field
    predicate   : (Carrier S) → Set _
    predWellDef : ∀ {x y : Carrier S}  → (_≈_ S) x y →
                                       predicate x → predicate y
\end{spec}

With a setoid predicate |P|, we can define a subsetoid:

\begin{spec}
SubSetoid : (S : Setoid _ _) → (P : SetoidPredicate S) → Setoid _ _
SubSetoid S P = record  { Carrier = Σ[ e ∈ Carrier S ] (predicate P e)
                        ; _≈_ = λ { (e₁ , _) (e₂ , _) → (_≈_ S) e₁ e₂ }
                        ; isEquivalence = {! !}
                        }
\end{spec}

\noindent We omit the proof of the relation is of equivalence.

Having implemented predicates and subsetoids, we can define the
condition necessary to construct a subalgebra.
We need a setoid predicate for each sort, and the condition asserting
that if we have a vector where each element satisfies the predicate
(i.e., all elements are in the subset), then applying an operation
results in an element that satisfies the predicate. 

\begin{spec}
record SubAlg (A : Algebra Σ) : Set _ where
  constructor _⊢⊣_
  field
    pr   : (s : sorts Σ) → SetoidPredicate (A ⟦ s ⟧ₛ)
    sacond : ∀  {ar} {s} → (f : ops Σ (ar , s)) →
                (_⇨v_ (predicate ∘ pr) ⟨→⟩ predicate (pr s))
                (_⟨$⟩_ (A ⟦ f ⟧ₒ))

\end{spec}

\noindent Function |_⇨v_| extends a predicate over vectors, and
function |_⟨→⟩_|, from standard library, expresses the condition
mentioned above.

With |SubAlg A| we can construct a $\Sigma$-algebra. The carriers are
elements in the subsetoid induced by the predicate |pr|, and for each
operation, we must give a function from a vector of elements in the
corresponding subsetoids to another element in a subsetoid.
The condition |sacond| ensures that we can give the proof that this
element satisfies the corresponding predicate.

\begin{spec}
  SubAlgebra : ∀ {Σ} {A} → SubAlg A → Algebra Σ
  SubAlgebra (Pₛ ⊢⊣ cond)  = (λ s → SubSetoid (A ⟦ s ⟧ₛ) (Pₛ s))
                           ∥ if
    where  if : ∀ {ar} {s} → (f : ops Σ (ar , s)) → _
           if f = record { _⟨$⟩_ = λ v →  (A ⟦ f ⟧ₒ ⟨$⟩ map (λ _ → proj₁) v)
                                          , cond f (vpred v)
\end{spec}

\noindent where |vpred| converts the vector v (of elements in the
subsetoids, i. e., pairs of an element and a predicate) to the extension
of predicates.
\manu{este último párrafo no está claro :-/}.

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
