\section{Equational Logic}

In this section we formalize (conditional) equational logic as
presented by \citet{goguen2005specifying}, extending the term algebra
with variables and introducing a formal system for conditional
equations; we show that this system is sound and complete.

\subsection{Free algebra with variables}
The first step to define equations is to add variables to the set of
terms. Given a signature |Σ|, we define |Vars Σ = sorts Σ → Set| as
the set of families of variables for |Σ| and for each |X : Vars Σ| we
define a new signature extending |Σ|, taking the variables as new constants
(i.e. , operations with arity []).
\begin{spec}
  _〔_〕 : (Σ : Signature) → (X : Vars Σ) → Signature
  Σ 〔 X 〕 = record  { sorts = sorts Σ ; ops =  ops' }
     where   ops' ([] , s)   = ops Σ ([] , s) ⊎ X s
             ops' (ar , s)   = ops Σ (ar , s)
\end{spec}%
\comment{In some literature this new signature is a special case of
  a more general construction where one takes the disjoint union of
  two signatures. A signature $\Sigma$ is said to be \emph{ground}
  if $\mathit{ops} \Sigma (ar , s) = \emptyset whenever ar \neq []$.
  This is a contrived generalization which does not seem to add much;
  for example, one needs that $X$ is a ground signature with the
  same sorts of $\Sigma$.
}%
Note that it's easy to refer to constant operations and extend them, thanks
to the way that we defined operations in a signature.

As we will see in the next section, an inclusion of signatures
$\Sigma \subseteq \Sigma'$ induces a contra-variant inclusion of
algebras; in the particular case of enlarging a signature with
variables we can make explicit the inclusion of the term algebras:
\begin{spec}
T_〔_〕 : (Σ : Signature) → (X : Vars Σ) → Algebra Σ
T Σ 〔 X 〕  = |T| (Σ 〔 X 〕) ⟦_⟧ₛ) ∥ io
  where  io {[]}  f  = |T| (Σ 〔 X 〕) ⟦ inj₁ f ⟧ₒ
         io {ar}  f  = |T| (Σ 〔 X 〕) ⟦ f ⟧ₒ
\end{spec}
We let |Env {Σ} X A = ∀ {s} → X s → ∥ A ⟦ s ⟧ₛ ∥ | be the set of
\emph{environments} from |X| to |A|; an environment |θ : Env X A|
yields a |Σ 〔 X 〕|-algebra by interpreting a variable |x| as |θ x|.
The free algebra |T Σ 〔 X 〕| has the universal
\emph{freeness} property: given a $\Sigma$-algebra $\mathcal{A}$
and an environment $\theta$, there exists an unique homomorphism |⟦_⟧θ|
from |T Σ 〔 X 〕| to $\mathcal{A}$ such that |⟦ x ⟧θ  = θ(x)| for
|x ∈ X|.%
\comment{Any |Σ 〔 X 〕|-algebra can be decomposed as |Σ|-algebra
  paired with an environment.}%
% A substitution of variables to terms is simply an environment
% of the term algebra |∣T∣ Σ 〔 X 〕|. 

% \begin{spec}
%   Subst : Set
%   Subst = Env X (T Σ 〔 X 〕)
% \end{spec}

\subsection{Equations, satisfactibility and provability}

\paragraph{Equations} In the mono-sorted setting an equation is a pair
of terms where all the variables are assumed to be universally
quantified and an equational theory is a (finite) set of equations. In
our multi-sorted framework we have \textit{sorted}
equations. Moreover, we allow for conditional equations
$t = t' \text{, if } t_1 = t'_1, \ldots, t_n = t'_n$; notice that
each condition $t_i = t'_i$ is of a given sort. \comment{In this section
we use in different contexts our definition of heterogeneous vectors:
to define the conditions of an equation, as the definition of a theory,
and, finally, as premises in rules of the deduction system.}

Let |Σ| be a signature and let |Eq Σ X s| be pairs of terms of sorts
|s|. A conditional equation is a tuple of the equation itself and the
list of conditions, since the conditions are sorted we also
need the list of sorts typing each condition.
\begin{spec}
record Equation (Σ ) (X : Vars Σ) (s : sorts Σ) : Set where
  constructor ⋀_if_
  field
    eq  :   Eq Σ X s
    cond : Σ[ carty ∈ Arity Σ ] (HVec (Eq Σ X) carty)
\end{spec}
\comment{\noindent Notice that we follow Goguen and Messeguer in that equations
are given explicitly over a set of variables. This, in turn, leads us
to define satisfability as proposed by Huet and Oppen.}
% \noindent The two terms of the equation are fields |left|
% and |right|. If the equation is conditional, we have a non-empty
% arity |carty| and two vectors of terms with arity |carty|.
% We can give a short notation for non-conditional equations:
% \begin{spec}
% ⋀_≈_ : ∀ {Σ X s} → (t t' : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥) → Equation Σ X s
% ⋀ t ≈ t' = ⋀ t ≈ t' if「 [] 」 (⟨⟩ , ⟨⟩)
% \end{spec}

A \emph{theory} over the signature $\Sigma$ is given by vector of equations.
\begin{spec}
Theory : (Σ : Signature) → (X : Vars Σ) → (ar : Arity Σ) → Set
Theory Σ X ar = HVec (Equation Σ X) ar
\end{spec}

\paragraph{Satisfaction} We recall that a $\Sigma$-algebra
$\mathcal{A}$ \emph{satisfies} a conditional equation
$t = t', \text{ if } t_1 = t'_1,\ldots,t_n=t'_n$ if for any
environment $\theta : X \to \mathcal{A}$, $⟦ t ⟧θ = ⟦ t' ⟧θ$, whenever
$⟦ t_i ⟧θ = ⟦ t'_i ⟧θ$ for $1 \leqslant i \leqslant n$.  In order to
formalize satisfaction we first define when an environment models an equation.
\begin{spec}
_,_⊨ₑ_ : ∀ {Σ X A} → (θ : Env X A) → (s : sorts Σ) → Eq Σ X s → Set
θ , s ⊨ₑ (t , t') = _≈_ (A ⟦ s ⟧ₛ) (⟦ t ⟧ θ) (⟦ t' ⟧ θ)
\end{spec}
\noindent Using the point-wise extension of the previous predicate we can
write directly the notion of satisfaction.
\begin{spec} 
_,_⊨_ : ∀ {Σ X} (A : Algebra Σ) → (s : sort Σ) → Equation Σ X s → Set
A , s ⊨ (⋀ eq if (_ , eqs)) = ∀ θ → (θ ,_⊨ₑ_) ⇨v eqs) → θ , s ⊨ₑ eq
\end{spec}

\noindent We say that $\mathcal{A}$ is a \emph{model} of the theory
$T$ if it satisfies each equation in $T$; as usual an equation is a
consequence of a theory, if every model of the theory, satisfies the
equation.
\begin{spec}
_⊨ₘ_ : ∀ {Σ X ar} → (A : Algebra Σ) → (E : Theory Σ X ar) → Set
A ⊨ₘ E = (A ,_⊨_) ⇨v E

_⊨Σ_ : ∀ {Σ X ar s} → (Theory Σ X ar) → (Equation Σ X s) → Set
_⊨Σ_ {Σ} {s = s} E e = (A : Algebra Σ) → A ⊨ₘ E → A , s ⊨ e
\end{spec}%
\comment{\noindent  We notice that we choose to formalize the notion of
satisfability defined by \citet{huet-oppen}.}%
%
\paragraph{Provability} As noticed by \citet{huet-rewrite}, the
definition of a sound deduction system for multi-sorted equality logic
is more subtle than expected. We formalize the system presented in
\citet{goguen2005specifying}, shown in Fig.~\ref{fig:deduction}, and prove
soundness and completeness with respect to the satisfaction given
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
Algebras. This example, taken from \citet{DBLP:conf/RelMiCS/RochaM08},
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
\noindent Here we use the notation of Equational reasoning from
standard library and the relevant actions of the substitution |σ₁| are
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

