\section{Equational Logic}
\label{sec:eqlog}

In this section we introduce the notion of (conditional) equational
theories and the corresponding notion of satisfiability of theories
by algebras. Moreover we formalize (conditional) equational logic as
presented by Goguen and Lin \cite{goguen2005specifying} and prove that
the deduction system is sound and complete.

\subsection{Free algebra with variables}
The term algebra we have just defined contained only \emph{ground}
terms, \ie terms without variables. Given a signature |Σ| and |X :
sorts Σ → Set| a family of variables, we define a new signature
extending |Σ| with |X| by taking the variables as new constants
(i.e. , operations with arity []).
\begin{spec}
  _〔_〕 : (Σ : Signature) → (X : sorts Σ → Set) → Signature
  Σ 〔 X 〕 = record  { sorts = sorts Σ ; ops =  ops' }
     where   ops' ([] , s)   = ops Σ ([] , s) ⊎ X s
             ops' (ar , s)   = ops Σ (ar , s)
\end{spec}%
\noindent Note that it is easy to refer to constant operations and
extend them, because we indexed the set of operations on their arity
and target sort.

It is easy to turn the term algebra of the extended signature
into an algebra for the original signature:
\begin{spec}
∣T∣_〔_〕 : (Σ : Signature) → (X : sorts Σ → Set) → Algebra Σ
∣T∣ Σ 〔 X 〕  = record { _⟦_⟧ₛ = |T| (Σ 〔 X 〕) ⟦_⟧ₛ , _⟦_⟧ₒ = io }
  where  io {[]}  f  = |T| (Σ 〔 X 〕) ⟦ inj₁ f ⟧ₒ
         io {ar}  f  = |T| (Σ 〔 X 〕) ⟦ f ⟧ₒ
\end{spec}
\noindent The only difference with the algebra of ground terms is that
we inject constants from |Σ| to distinguish them from variables. In
order to interpret terms with variables we need \emph{environments} to
give meaning to variables.

We let |Env X A = ∀ {s} → X s → ∥ A ⟦ s ⟧ₛ ∥ | be the set of
environments from |X| to |A|.  The free algebra | ∣T∣ Σ 〔 X 〕| has the
universal \emph{freeness} property: given |A : Algebra Σ| and an
environment |θ : Env X A|, there exists an unique homomorphism |⟦_⟧θ :
Homo (∣T∣ Σ 〔 X 〕) A| such that |⟦ x ⟧θ = θ(x)| for |x ∈ X|.

\subsection{Equations, satisfiability, and provability}

\paragraph{Equations} In the mono-sorted setting an equation is a pair
of terms where all the variables are assumed to be universally
quantified and an equational theory is a (finite) set of equations.
In a  multi-sorted setting both sides of an equation should be terms
of the same sort. Moreover we allow quasi-identities which we
write as conditional equations:
\[ t = t'\ \mathsf{if} \  t_1 = t'_1, \ldots, t_n = t'_n \enspace . \] 

Let |Σ| be a signature and |X : sorts Σ → Set| be a family of
variables for |Σ|. An identity |e : Eq Σ X s| is a pair of (open)
terms with sort |s|. A conditional equation is modelled as record with
fields for the conclusion and the conditions, modelled as an
heterogeneous vector of sorted identities . We declare a constructor
to use the lighter notation |⋀ eq if (ar , eqs)| instead of |record {
  eq = e ; cond = (ar , eqs )}|. \vspace{-6pt}
\begin{spec}
record Equation (Σ : Signature) (X : sorts Σ → Set) (s : sorts Σ) : Set where
  constructor ⋀_if_
  field
    eq     :   Eq Σ X s
    cond   :   Σ[ ar ∈ List (sorts Σ) ] (HVec (Eq Σ X) ar)
\end{spec}
\noindent A \emph{theory} over the signature $\Sigma$ is given by a
vector of conditional equations.
\begin{spec}
Theory : (Σ : Signature) → (X : sorts Σ → Set) → (ar : List (sorts Σ)) → Set
Theory Σ X ar = HVec (Equation Σ X) ar
\end{spec}
Notice that in our formalization all the equations of a theory share
the same set of variables, in contrast with Goguen' and Meseguer's
calculus where each equation has its own set of quantified variables.
\comment{\noindent Notice that we follow Goguen and Meseguer in that equations
are given explicitly over a set of variables. This, in turn, leads us
to define satisfiability as proposed by Huet and Oppen.}

\paragraph{Satisfiability} Let $\Sigma$ be a signature and
$\mathcal{A}$ be an algebra for $\Sigma$. We say that a conditional equation
$t = t'\ \mathsf{if}\ t_1 = t'_1,\ldots,t_n=t'_n$ is
\emph{satisfied} by $\mathcal{A}$ if for any
environment $\theta : X \to \mathcal{A}$, $⟦ t ⟧θ = ⟦ t' ⟧θ$, whenever
$⟦ t_i ⟧θ = ⟦ t'_i ⟧θ$ for $1 \leqslant i \leqslant n$. In order to
formalize satisfiability we first define when an environment models an
equation.
\begin{spec}
_⊨ₑ_ : ∀ {Σ X A} → (θ : Env X A) → {s : sorts Σ} → Eq Σ X s → Set
_⊨ₑ_ θ {s} (t , t') = _≈_ (A ⟦ s ⟧ₛ) (⟦ t ⟧ θ) (⟦ t' ⟧ θ)
\end{spec}
\noindent Using the point-wise extension of this relation we can write
directly the notion of satisfiability.
\begin{spec} 
_⊨_ : ∀ {Σ X} (A : Algebra Σ) → {s : sorts Σ} → Equation Σ X s → Set
A ⊨ (⋀ eq if (_ , eqs)) = ∀ θ → ((θ ⊨ₑ_)* eqs) → θ ⊨ₑ eq
\end{spec}

\noindent We say that $\mathcal{A}$ is a \emph{model} of the theory
$E$ if it satisfies each equation in $E$. As usual an equation is a
logical consequence of a theory, if every model of the theory
satisfies the equation.
\begin{spec}
_⊨ₘ_ : ∀ {Σ X ar} → (A : Algebra Σ) → (E : Theory Σ X ar) → Set
A ⊨ₘ E = (A ,_⊨_)* E

_⊨Σ_ : ∀ {Σ X ar s} → (E : Theory Σ X ar) → (e : Equation Σ X s) → Set
_⊨Σ_ {Σ} E e = (A : Algebra Σ) → A ⊨ₘ E → A ⊨ e
\end{spec}%
\comment{\noindent  We notice that we choose to formalize the notion of
satisfiability defined by \citet{huet-oppen}.}%
%
\paragraph{Provability} As noticed by Huet and Oppen
\cite{huet-rewrite}, the definition of a sound deduction system for
multi-sorted equality logic is more subtle than expected. We formalize
the system presented in \cite{goguen2005specifying}, shown in
Fig.~\ref{fig:deduction}. The first three rules are reflexivity,
symmetry and transitivity; the fourth rule, called substitution, allows to instantiate an
axiom with a substitution |σ|, provided one has proofs for every
condition of the axiom; finally, the last rule internalizes Leibniz rule, for
replacing equals by equals in subterms.  Notice that we can only prove
identities and not quasi-identities.
%Notice the absence of a rule for deducing
%axioms as they are, in general, conditional equations.
\begin{figure}[t]
  \centering
  \bottomAlignProof
  \AxiomC{}
  \UnaryInfC{$E \vdash \forall X,\, t = t$}
  \DisplayProof\hspace{2ex}
%
  \bottomAlignProof
  \AxiomC{$E \vdash \forall X,\, t_0 = t_1$}
  \UnaryInfC{$E \vdash \forall X,\, t_1 = t_0$}
  \DisplayProof \hspace{2ex}
% 
 \bottomAlignProof
 \AxiomC{$E \vdash \forall X,\, t_0 = t_1$}
  \AxiomC{$E \vdash \forall X,\, t_1 = t_2$}
  \BinaryInfC{$E \vdash \forall X,\, t_0 = t_2$}
  \DisplayProof
\\[6pt]
  \AxiomC{$\forall X,\,t = t' \ \mathsf{if}\
      t_1=t'_1,\ldots, t_n=t'_n \in E$}
  \AxiomC{$E \vdash \forall X,\,\sigma(t_i) = \sigma(t'_i)$}
  \RightLabel{$\sigma \colon X \rightarrow E_\Sigma(X)$}
  \BinaryInfC{$E \vdash \forall X,\, \sigma(t) = \sigma(t')$}
  \DisplayProof
\\[6pt]
  \AxiomC{$E \vdash \forall X,\, t_1 = t'_1$}
  \AxiomC{$\cdots$}
  \AxiomC{$E \vdash \forall X,\, t_n = t'_n$}
  \RightLabel{$f : [s_1,...,s_{n}] \Rightarrow_{\Sigma} s$}
  \TrinaryInfC{$E \vdash \forall X,\, f\,(t_1,\ldots,t_n) = f\,(t'_1,\ldots,t'_n)$}
  \DisplayProof
  \caption{Deduction system}
  \label{fig:deduction}
\end{figure}
We define the relation of provability as an inductive type,
parameterized in the theory |E|, and indexed by the conclusion of the
proof. For conciseness, we only show the constructor for transitivity:
\begin{spec}
data _⊢_ {Σ X ar} (E : Theory Σ X ar) : ∀ {s} → Eq Σ X s → Set where
    ptrans : ∀    {s} {t₀ t₁ t₂} →
                  E ⊢ (t₀ , t₁) → E ⊢ (t₁ , t₂) → E ⊢ (t₀ , t₂)
\end{spec}

Let |E| be a theory over a signature |Σ|. It is straightforward to
define a setoid over |∣T∣ Σ 〔 X 〕| by letting |t₁ ≈ t₂| if |E ⊢ t₁ ≈
t₂|; this equivalence relation (thanks to the first three rules) is a
congruence (because of the last rule) over the term algebra. We can
also use the facility provided by the standard library to write
proofs with several transitive steps more nicely, as can be seen
in the next example.

The proofs of soundness and completeness are proved as in the
mono-sorted case. For soundness one proceeds by induction on the
derivations; completeness is a consequence that the quotient of the
term algebra by provable equality is a model.
\begin{theorem}[Soundness and Completeness]
  $E \vdash t ≈ t'$ iff $E \models_{\Sigma} t ≈ t'$.
\end{theorem}

Let $E$ and $E'$ be two theories over the signature $\Sigma$. We say
that $E$ is \emph{stronger} than $E'$ if every axiom $e \in E'$ can be
deduced from $E$, written $E \vdash\!\!\text{\textmd{T}} E'$.  Obviously if $E$
is stronger than $E'$, then any equation that can be deduced from $E'$
can also be deduced from $E$ and any model of $E$ is also a model of
$E'$

\subsection{A theory for Boolean Algebras }
As an example we show a fragment (the full code is available in the
cited URL) of the formalization of a Boolean Theory discussed in
\cite{DBLP:conf/RelMiCS/RochaM08}.  The signature is mono-sorted, so
we use the unit type as its only sort.\vspace{-6pt}
\begin{spec}
data bool-ops : List ⊤ × ⊤ → Set where
  f t    : bool-ops ([] ↦ tt)
  neg  : bool-ops ([ tt ] ↦ tt)
  and or  : bool-ops (([ tt , tt ]) ↦ tt)

bool-sig : Signature
bool-sig = record { sorts = ⊤ ; ops = bool-ops }
\end{spec}
We let |X tt = ℕ| be the set of variables, and let |Form|
stand for terms over |bool-sig 〔 Vars 〕| with the
following smart-constructors:\vspace{-6pt}
\begin{spec}
true false : Form
true = term (inj₁ t) ⟨⟩
false = term (inj₁ f) ⟨⟩

p q  : Form
p = term (inj₂ 0) ⟨⟩
q = term (inj₂ 1) ⟨⟩

_∧_ : Form → Form → Form
φ ∧ ψ = term and ⟨⟨ φ , ψ ⟩⟩

¬ : Form → Form
¬ φ = term neg ⟨⟨ φ ⟩⟩
\end{spec}
\noindent We show only two of the twelve axioms of the theory |E-Bool|:\vspace{-6pt}
\begin{spec}
commAnd leastDef : Equation bool-sig Vars tt
commAnd = ⋀ (p ∧ q) ≈ (q ∧ p) if ([] , ⟨⟩)
leastDef = ⋀ (p ∧ (¬ p)) ≈ false  if ([] , ⟨⟩)

E-bool : Theory bool-sig Vars [ tt , tt , … ]
E-bool = ⟨ commAnd , leastDef , … ⟩
\end{spec}
\noindent The following example shows an equational proof using the
facility for equational reasoning provided by the standard library of
Agda. In the justification steps we use the substitution rule (called
|psubst|) and the pattern-synonyms |commAndAx,leastDefAx| as short-hands for
|commAnd ∈ E-bool| and |leastDef ∈ E-bool|, respectively.\vspace{-6pt}
\begin{spec}
  p₁ : E-bool ⊢ (⋀ ¬ p ∧ p ≈ false)
  p₁ = begin
         ¬ p ∧ p
         ≈⟨ psubst commAndAx σ₁ ∼⟨⟩ ⟩
         p ∧ ¬ p
         ≈⟨ psubst leastDefAx idSubst ∼⟨⟩ ⟩
         false
       ∎
\end{spec}
\noindent The relevant actions of the substitution |σ₁| are |σ₁ p = ¬
p| and | σ₁ q = p|. 

% The first step is performed by the |psubst| rule, with the
% first axiom of theory |Tbool₁|, the commutativity of conjunction.
% The substitution used consists of mapping the first variable
% (whose term we called |p|) to the term
% resulting of the negation of that variable, i. e., |¬ p|. And mapping
% the second variable (whose term we called |q|) to the first one (|p|).
% For the rest, we can define the identity substitution.
% Once we proved the first step, the conclusion is exactly the left side
% of the second axiom, so we can use |psubst| rule with the identity
% substitution.

