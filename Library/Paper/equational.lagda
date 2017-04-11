\section{Equational Logic}

In this section we formalize (conditional) equational logic as
presented by \citet{goguen2005specifying}, extending the term algebra
with variables and introducing a formal system for conditional
equations; we show that this system is sound and complete.

\subsection{Free algebra with variables}
The first step to define equations is to add variables to the set of
terms. Given a signature |Σ|, we say that |X : sorts Σ → Set| is a
family of variables for |Σ|, we let |Vars Σ = sorts Σ → Set|. For each
family |X : Vars Σ| we enlarge the signature by taking the variables as
new constants (\ie, operations with arity |[]|).
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
\citet{goguen2005specifying}, shown in \ref{fig:deduction}, and prove
soundness and completeness with respect to the satisfaction given
before. The first three rules are reflexivity, symmetry and transitivity;
the fourth rule is substitution and allows to
use axioms (notice the absence of a rule for deducing
axioms as they are, in general, conditional equations); finally,
the last rule internalizes Leibniz rule, for replacing equals
by equals.
\begin{figure}[t]
  \centering
  \begin{alignat*}{1}
      \inferrule*{ }{T \vdash (\forall X)\, t = t}\quad &
      \inferrule*{ T \vdash (\forall X)\, t = t'}
        {T \vdash (\forall X)\, t' = t}  \quad
      \inferrule*{T \vdash (\forall X)\, t_0 = t_1 \\ 
              T \vdash (\forall X)\, t_1 = t_2}
              {T \vdash (\forall X)\, t_0 = t_2} \\
    &\inferrule*{(\forall X) t = t' \,\text{if}\,
      t_1=t'_1,\ldots, t_n=t'_n \in T\ \ 
      T \vdash \forall X, \sigma(t_i) = \sigma(t'_i)
    }{T \vdash \forall X, \sigma(t) = \sigma(t')} 
    \\
    &\inferrule*{T \vdash (\forall X)\, t_i = t'_i}
              {T \vdash (\forall X)\, f\,(t_1,\ldots,t_n) = f\,(t'_1,\ldots,t'_n)}
  \end{alignat*}
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
% It's straightforward to define a setoid, where the carrier are the
% terms of |Σ 〔 X 〕|, and the relation is a proof of equality of
% two terms.
The proofs of soundness and completeness are proved as in the
mono-sorted case; the first one proceeds by induction on the
derivations, while the second is a consequence that the set of
terms quotiened by provable equality is a model.
\begin{theorem}[Soundness and Completeness]
  $T \vdash t ≈ t'$ iff $T \models_{\Sigma} t ≈ t'$.
\end{theorem}
The formal statement and the proofs of this theorem is almost as in
paper. We remark, however, that one cannot speak of all the algebras
satisfying some predicate (for example, being the model of a theory),
but only of the algebras of some levels.

Let $T$ and $T'$ be two $\Sigma$-theories, we say that $T$ is
\emph{stronger} than $T'$ if every axiom $e \in T'$ can be deduced
from $T$.
\begin{spec}
_≤ₜ_ : ∀ {Σ X ar ar'} → Theory Σ X ar → Theory Σ X ar' → Set
T' ≤ₜ T =  ∀ {ar eqs s eq} → (⋀ eq if (_ , eqs)) ∈ T' →
             (T ⊢_) ⇨v eqs → T ⊢ eq
\end{spec}
\noindent This order of theories is preserved by models: if $T$ is stronger
than $T'$ any model of $T$ is also a model of $T'$. In particular, equivalent
theories have the same models.
\begin{spec}
⊨≤ₜ : ∀  {Σ X A ar ar'} {T T'} → T' ≤ₜ T → A ⊨ₘ T → A ⊨ₘ T'
⊨≤ₜ T' T p⇒ A model = ?
\end{spec}
    

\subsection{An example}

Lets consider a boolean equational theory. The language consists of
two constants $t$ and $f$, one unary operator $\neg$ and two binary
operators $\wedge , \vee$.

\begin{spec}
data Σops₁ : List ⊤ × ⊤ → Set where
  t₁    : Σops₁ ([] ↦ tt)
  f₁    : Σops₁ ([] ↦ tt)
  neg₁  : Σops₁ ([ tt ] ↦ tt)
  and₁  : Σops₁ (([ tt , tt ]) ↦ tt)
  or₁   : Σops₁ (([ tt , tt ]) ↦ tt)

Σbool₁ : Signature
Σbool₁ = ⟨ ⊤ , Σops₁ ⟩
\end{spec}

\noindent This signature is monosorted. Type |⊤| is the unit type of
agda, which has exactly one inhabitant.

In order to define a theory in our formalization, we have to choose
a set of variables for each sort. In this case, we have only one sort.
We use natural numbers as variables:

\begin{spec}
Vars₁ : Vars Σbool₁
Vars₁ _ = ℕ
\end{spec}

The formulas of this boolean logic are terms in the term algebra of
|Σbool₁ 〔 Vars₁ 〕|. We define smart constructors for this formulas:

\begin{spec}
Form₁ : Set
Form₁ = HU (Σbool₁ 〔 Vars₁ 〕) tt

_∧₁_ : Form₁ → Form₁ → Form₁
φ ∧₁ ψ = term and₁ ⟨⟨ φ , ψ ⟩⟩

_∨₁_ : Form₁ → Form₁ → Form₁
φ ∨₁ ψ = term or₁ ⟨⟨ φ , ψ ⟩⟩

¬ : Form₁ → Form₁
¬ φ = term neg₁ ⟨⟨ φ ⟩⟩

p : Form₁
p = term (inj₂ 0) ⟨⟩

q : Form₁
q = term (inj₂ 1) ⟨⟩

true₁ : Form₁
true₁ = term (inj₁ t₁) ⟨⟩

false₁ : Form₁
false₁ = term (inj₁ f₁) ⟨⟩
\end{spec}

\noindent |p|, |q| and |r| are smart constructors for three variables,
necessary to define the axioms.

The theory consists of 12 axioms. We show only two of them:
Commutativity of $\wedge$, and the definition of $f$:

\begin{spec}
commAnd₁ : Eq₁
commAnd₁ = ⋀ p ∧₁ q ≈ (q ∧₁ p)

andF : Eq₁
andF = ⋀ p ∧₁ (¬ p) ≈ false₁

Tbool₁ : Theory Σbool₁ Vars₁ [ tt , tt ]
Tbool₁ = ⟪ commAnd₁ , andF ⟫

pattern ax₁ = here
pattern ax₂ = there here
\end{spec}

\noindent We define two patterns for constructors of the type |_∈_|,
necessary if we need to use the rule |psubst|.

Let see a proof of the equation |⋀ ¬ p ∧₁ p ≈ false₁|. The axiom
|andF| expresses something similar, but the operands in the left side
are inverted. We can use first the commutativity axiom and then
axiom |andF|:

\begin{spec}
  p₁ : Tbool₁ ⊢ (⋀ ¬ p ∧₁ p ≈ false₁)
  p₁ = begin
         ¬ p ∧₁ p
         ≈⟨ psubst ax₁ σ₁ ∼⟨⟩ ⟩
         p ∧₁ ¬ p
         ≈⟨ psubst ax₂ idSubst ∼⟨⟩ ⟩
         false₁
       ∎
    where σ₁ : Subst
          σ₁ 0 = ¬ p
          σ₁ 1 = p
          σ₁ n = term (inj₂ n) ⟨⟩
\end{spec}

\noindent We use the notation of Equational reasoning from standard
library. The first step is performed by the |psubst| rule, with the
first axiom of theory |Tbool₁|, the commutativity of conjunction.
The substitution used consists of mapping the first variable
(whose term we called |p|) to the term
resulting of the negation of that variable, i. e., |¬ p|. And mapping
the second variable (whose term we called |q|) to the first one (|p|).
For the rest, we can define the identity substitution.
Once we proved the first step, the conclussion is exactly the left side
of the second axiom, so we can use |psubst| rule with the identity
substitution.

