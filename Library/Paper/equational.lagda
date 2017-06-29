\section{Equational Logic}
\label{sec:eqlog}


In this section we introduce the notion of (conditional) equational
theories and the corresponding notion of satisfiability of theories
by algebras. Moreover we formalize (conditional) equational logic as
presented by Goguen and Lin \cite{goguen2005specifying} and prove that
the deduction system is sound and complete.

\subsection{Free algebra with variables}
The term algebra we have just defined contained only \emph{ground}
terms, \ie terms without variables; now we enlarge terms by allowing
variables. Given a signature |Σ| and |X : sorts Σ → Set| a families of
variables, we define a new signature extending |Σ| by taking the
variables as new constants (i.e. , operations with arity []).
\begin{spec}
  _〔_〕 : (Σ : Signature) → (sorts Σ → Set) → Signature
  Σ 〔 X 〕 = record  { sorts = sorts Σ ; ops =  ops' }
     where   ops' ([] , s)   = ops Σ ([] , s) ⊎ X s
             ops' (ar , s)   = ops Σ (ar , s)
\end{spec}%
\noindent Note that it is easy to refer to constant operations and
extend them, because we indexed the set of operations on their arity
and target sort.

As we will see in the next section, an inclusion of signatures
$\Sigma \subseteq \Sigma'$ induces a contra-variant inclusion of
algebras. In the particular case of enlarging a signature with
variables we can make explicit the inclusion of the term algebras:
\begin{spec}
∣T∣_〔_〕 : (Σ : Signature) → (sorts Σ → Set) → Algebra Σ
∣T∣ Σ 〔 X 〕  = |T| (Σ 〔 X 〕) ⟦_⟧ₛ) ∥ io
  where  io {[]}  f  = |T| (Σ 〔 X 〕) ⟦ inj₁ f ⟧ₒ
         io {ar}  f  = |T| (Σ 〔 X 〕) ⟦ f ⟧ₒ
\end{spec}
\noindent The only difference with the algebra of ground terms is that
we inject constants from |Σ| to distinguish them from variables. In
order to interpret terms with variable we need \emph{environments} to
give meaning to variables.

We let |Env {Σ} X A = ∀ {s} → X s → ∥ A ⟦ s ⟧ₛ ∥ | be the set of
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
\[ t = t' \text{, if } t_1 = t'_1, \ldots, t_n = t'_n \enspace . \] 

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
Theory : (Σ : Signature) → (sorts Σ → Set) → (ar : List (sorts Σ)) → Set
Theory Σ X ar = HVec (Equation Σ X) ar
\end{spec}
Notice that in our formalization all the equations of a theory share
the same set of variables, in contrast with Goguen' and Meseguer's
calculus where each equation has its own set of quantified variables.
\comment{\noindent Notice that we follow Goguen and Messeguer in that equations
are given explicitly over a set of variables. This, in turn, leads us
to define satisfability as proposed by Huet and Oppen.}

\paragraph{Satisfiability} Let $\Sigma$ be a signature and
$\mathcal{A}$ be an algebra for $\Sigma$. $\mathcal{A}$
\emph{satisfies} a conditional equation
$t = t', \text{ if } t_1 = t'_1,\ldots,t_n=t'_n$ if for any
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
$T$ if it satisfies each equation in $T$. As usual an equation is a
logical consequence of a theory, if every model of the theory
satisfies the equation.
\begin{spec}
_⊨ₘ_ : ∀ {Σ X ar} → (A : Algebra Σ) → (E : Theory Σ X ar) → Set
A ⊨ₘ E = (A ,_⊨_)* E

_⊨Σ_ : ∀ {Σ X ar s} → (Theory Σ X ar) → (Equation Σ X s) → Set
_⊨Σ_ {Σ} E e = (A : Algebra Σ) → A ⊨ₘ E → A ⊨ e
\end{spec}%
\comment{\noindent  We notice that we choose to formalize the notion of
satisfability defined by \citet{huet-oppen}.}%
%
\paragraph{Provability} As noticed by Huet and Oppen \cite{huet-rewrite}, the
definition of a sound deduction system for multi-sorted equality logic
is more subtle than expected. We formalize the system presented in
\cite{goguen2005specifying}, shown in Fig.~\ref{fig:deduction}, and prove
soundness and completeness with respect to the satisfiability given
before. The first three rules are reflexivity, symmetry and
transitivity; the fourth rule allows to use
axioms where is applied a substitution $\sigma$; finally, the last rule
internalizes Leibniz rule, for replacing equals by equals in subterms.

%Notice the absence of a rule for deducing
%axioms as they are, in general, conditional equations.
\begin{figure}[t]
  \centering
  \bottomAlignProof
  \AxiomC{}
  \UnaryInfC{$T \vdash \forall X,\, t = t$}
  \DisplayProof\hspace{2ex}
%
  \bottomAlignProof
  \AxiomC{$T \vdash \forall X,\, t_0 = t_1$}
  \UnaryInfC{$T \vdash \forall X,\, t_1 = t_0$}
  \DisplayProof \hspace{2ex}
% 
 \bottomAlignProof
 \AxiomC{$T \vdash \forall X,\, t_0 = t_1$}
  \AxiomC{$T \vdash \forall X,\, t_1 = t_2$}
  \BinaryInfC{$T \vdash \forall X,\, t_0 = t_2$}
  \DisplayProof
\\[6pt]
  \AxiomC{$\forall X,\,t = t' \,\text{if}\,
      t_1=t'_1,\ldots, t_n=t'_n \in T$}
  \AxiomC{$T \vdash \forall X,\,\sigma(t_i) = \sigma(t'_i)$}
  \RightLabel{$\sigma \colon X \rightarrow T_\Sigma(X)$}
  \BinaryInfC{$T \vdash \forall X,\, \sigma(t) = \sigma(t')$}
  \DisplayProof
\\[6pt]
  \AxiomC{$T \vdash \forall X,\, t_1 = t'_1$}
  \AxiomC{$\cdots$}
  \AxiomC{$T \vdash \forall X,\, t_n = t'_n$}
  \RightLabel{$f : [s_1,...,s_{n}] \Rightarrow_{\Sigma} s$}
  \TrinaryInfC{$T \vdash \forall X,\, f\,(t_1,\ldots,t_n) = f\,(t'_1,\ldots,t'_n)$}
  \DisplayProof
  \caption{Deduction system}
  \label{fig:deduction}
\end{figure}
We define the relation of provability as an inductive type,
parameterized in the theory |T|, and indexed by the equation that is
the conclusion of the proof. For conciseness, we only show the
constructor for the transitivity rule:
\begin{spec}
data _⊢_ {Σ X ar} (E : Theory Σ X ar) : ∀ {s} → Eqn Σ X s → Set where
    ptrans : ∀    {s} {t₀ t₁ t₂ : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥} →
                  E ⊢ t₀ ≈ t₁ → E ⊢ t₁ ≈ t₂ → E ⊢ t₀ ≈ t₂
\end{spec}
It is straightforward to define a setoid over |T Σ 〔 X 〕| with
provable equality as the equivalence relation; this is useful for
using Agda's equational reasoning when constructing proofs.

The proofs of soundness and completeness are proved as in the
mono-sorted case; the first one proceeds by induction on the
derivations, while the second is a consequence that the quotient of
the set of terms by provable equality is a model.
\begin{theorem}[Soundness and Completeness]
  $T \vdash t ≈ t'$ iff $T \models_{\Sigma} t ≈ t'$.
\end{theorem}
The formal statement and the proofs of this theorem is almost as in
paper.
% Let $T$ and $T'$ be two $\Sigma$-theories, we say that $T$ is
% \emph{stronger} than $T'$ if every axiom $e \in T'$ can be deduced
% from $T$.
% \begin{spec}
% _≤ₜ_ : ∀ {Σ X ar ar'} → Theory Σ X ar → Theory Σ X ar' → Set
% T' ≤ₜ T =  ∀ {ar eqs s eq} → (⋀ eq if (_ , eqs)) ∈ T' →
%              (T ⊢_) ⇨v eqs → T ⊢ eq
% \end{spec}
% \noindent Obviously if $T$ is stronger than $T'$, then any equation that can
% be deduced from $T'$ can also be deduced from $T$. From which we conclude
% \begin{enumerate*}[label=(\roman*),itemjoin={}]
% \item any model of $T$ is also a model of $T'$, and
% \item equivalent theories have the same models.
% \end{enumerate*}
% \begin{spec}
% ⊨≤ₜ : ∀  {Σ X A ar ar'} {T T'} → T' ≤ₜ T → A ⊨ₘ T → A ⊨ₘ T'
% ⊨≤ₜ T' T p⇒ A model = ?
% \end{spec}
    
\subsection{A theory for Boolean Algebras }
In this section we show how to encode an axiomatization of Boolean
Algebras. This example, taken from \cite{DBLP:conf/RelMiCS/RochaM08},
shows that it is easy to specify equational theories in our framework.
Since the signature is mono-sorted, we use the unit type |⊤|, whose
only inhabitant is |tt|, as the only sort.
\begin{spec}
data boolOps : List ⊤ × ⊤ → Set where
  f t    : boolOps ([] ↦ tt)
  neg  : boolOps ([ tt ] ↦ tt)
  and or  : boolOps (([ tt , tt ]) ↦ tt)

Σbool : Signature
Σbool = record { sorts = ⊤ ; ops = boolOps }
\end{spec}
We let |Vars ⊤ = ℕ| be the set of variables and write |Form|
as an abbreviation for |HU (Σbool 〔 Vars 〕) tt|, for which we define some smart constructors:
\begin{spec}
true false : Form
true = term (inj₁ t) ⟨⟩
false = term (inj₁ f) ⟨⟩

p q r  : Form
p = term (inj₂ 0) ⟨⟩
q = term (inj₂ 1) ⟨⟩
r = term (inj₂ 2) ⟨⟩

_∧_ _∨_ : Form → Form → Form
φ ∧ ψ = term and ⟨⟨ φ , ψ ⟩⟩
φ ∨ ψ = term or ⟨⟨ φ , ψ ⟩⟩

¬ : Form → Form
¬ φ = term neg ⟨⟨ φ ⟩⟩
\end{spec}
\noindent We show only two of the twelve theorems of the theory |TBool|, the commutativity of meet and the definition of the
least element:
\begin{spec}
commAnd leastDef : Equation Σbool Vars tt
commAnd = ⋀ (p ∧ q) ≈ (q ∧ p)
leastDef = ⋀ (p ∧ (¬ p)) ≈ false

Tbool : Theory Σbool Vars [ tt , tt , … ]
Tbool = ⟨ commAnd , leastDef , … ⟩
\end{spec}
\noindent To use the substitution rule (called |psubst|),
we need to refer to the axioms
of the theory; in the formalization this is achieved by a proof that
the axiom is in the theory, by using pattern-synonyms we can refer to
the axioms by a more convenient (and conventional) name:
\begin{spec}
pattern commAndAx  = here
pattern leastDefAx = there here
\end{spec}
We show the equational proof for |⋀ ¬ p ∧ p ≈ false|.
\begin{spec}
  p₁ : Tbool ⊢ (⋀ ¬ p ∧ p ≈ false)
  p₁ = begin
         ¬ p ∧ p
         ≈⟨ psubst commAndAx σ₁ ∼⟨⟩ ⟩
         p ∧ ¬ p
         ≈⟨ psubst leastDefAx idSubst ∼⟨⟩ ⟩
         false
       ∎
\end{spec}
\noindent Here we use the notation of equational reasoning from
the standard library and the relevant actions of the substitution |σ₁| are
|σ₁ p = ¬ p| and | σ₁ q = p|. 

% The first step is performed by the |psubst| rule, with the
% first axiom of theory |Tbool₁|, the commutativity of conjunction.
% The substitution used consists of mapping the first variable
% (whose term we called |p|) to the term
% resulting of the negation of that variable, i. e., |¬ p|. And mapping
% the second variable (whose term we called |q|) to the first one (|p|).
% For the rest, we can define the identity substitution.
% Once we proved the first step, the conclussion is exactly the left side
% of the second axiom, so we can use |psubst| rule with the identity
% substitution.

