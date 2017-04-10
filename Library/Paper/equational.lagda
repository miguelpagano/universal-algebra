\section{Equational Logic}

In this section we formalize (conditional) equational logic, extending
the term algebra with variables and introducing a formal system for
conditional equations; we show that this system is sound and complete.
This section can be seen as a formalization of the system
proposed by \citet{goguen-equational}.

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
_⊨_ : ∀ {Σ X} (A : Algebra Σ) → (s : sort Σ) → Equation Σ X s → Set
A , s ⊨ (⋀ eq if (_ , eqs)) = ∀ θ → (θ ,_⊨ₑ_) ⇨v eqs) → θ , s ⊨ₑ eq
\end{spec}

\noindent We say that $\mathcal{A}$ is a \emph{model} of the theory
$T$ if it satisfies each equation in $T$.
\begin{spec}
_⊨ₜ_ : ∀ {Σ X ar} → (A : Algebra Σ) → (E : Theory Σ X ar) → Set
A ⊨ₜ E = (A ,_⊨_) ⇨v E
\end{spec}

\paragraph{Provability.}
Now we proceed to define equational proofs. Given a $\Sigma$-theory
$T$, a $\Sigma$-equation $e$ is provable if it is the conclusion of one
of the next rules:

\begin{itemize}
  \item[*] $T \vdash (\forall X)\, t = t$
  \item[*] If $T \vdash (\forall X)\, t = t'$, then
              $T \vdash (\forall X)\, t' = t$
  \item[*] If $T \vdash (\forall X)\, t_0 = t_1$ and
              $T \vdash (\forall X)\, t_1 = t_2$, then
              $T \vdash (\forall X)\, t_0 = t_2$
  \item[*] If $(\forall X) t = t' \,\text{if}\,
              u_1=u'_1,..., u_n=u'_n \in T$,
              $\sigma$ is a substitution and
              $T \vdash (\forall X)\, \sigma(u_i) = \sigma(u'_i)$,
              for $1 \leq i \leq n$, then
              $T \vdash (\forall X)\, \sigma(t) = \sigma(t')$
  \item[*] If $T \vdash (\forall X)\, t_i = t'_i$, with each $t_i$ term
              of sort $s_i$, for $1 \leq i \leq n$, and
              $f : [s_1,...,s_n] \Rightarrow s$ is an operation of
              $\Sigma$, then
              $T \vdash (\forall X)\, f\,(t_1,...,t_n) = f\,(t'_1,...,t'_n)$           
\end{itemize}

\noindent The first three rules are reflexivity, symetry and
          transitivity, so the relation is of equivalence.
          Next rule is often called \textit{substitution}, and allows
          to apply an axiom by replacing variables by terms. The last
          rule is often called \textit{replacement}, and allows us to
          apply equalities on subterms.

We define the relation of provability with an inductive type,
parameterized in the theory |T|, and indexed by the equation that is
the conclusion of the proof. We omit the definitions for reasons of space:

\begin{spec}
data _⊢_ {Σ X}  {ar : Arity Σ} (E : Theory Σ X ar) :
                {s : sorts Σ} → Equation Σ X s → Set where
  prefl   : ...
  psym    : ...
  ptrans  : ...
  psubst  : ...
  preemp  : ...
\end{spec}

It's straightforward to define a setoid, where the carrier are the
terms of |Σ 〔 X 〕|, and the relation is a proof of equality of
two terms.


\subsection{Correctness and completeness}

We can prove now, that having a proof of an equation $e$ in a theory, and
that all model of the theory satisfies $e$, are equivalent. This corresponds
with proofs of soundness and completeness of the equational calculus presented.

\paragraph{Soundness.} If an equation $e$ is provable in a theory
$T$, then for all $\Sigma$-algebra $\mathcal{A}$ that satisfies the
axioms in $T$, $\mathcal{A}$ satisfies $e$.

\begin{spec}
  soundness :  ∀ {Σ X} {ar} {s} {T : Theory Σ X ar} {e : Equation Σ X s}
                 → T ⊢ e → (A : Algebra Σ) → A ⊨T E → A ⊨ e
  soundness : ...
\end{spec}

\paragraph{Completeness.} 
If all $\Sigma$-algebra $\mathcal{A}$ that satisfies the axioms in $T$,
$\mathcal{A}$ satisfies an equation $e$, then $e$ is provably in $T$.

\begin{spec}
complete : ∀ {Σ X} {ar : Arity Σ} {s : sorts Σ} {E : Theory Σ X ar}
{e : Equation Σ X s} → ((A : Algebra Σ) → A ⊨T E → A ⊨ e) → E ⊢ e
complete = ...
\end{spec}

\manu{Ver qué podemos decir de esas pruebas. Quizás contar la idea de
la prueba de completitud.}

\subsection{Theory implication}
Let $T_1$ and $T_2$ be two $\Sigma$-theories, we say that $T_1$ implies
$T_2$ if for each axiom $e \in T_2$ there exists a proof
$T_1 \vdash (\forall X)\, e$.

\begin{spec}
_⇒T_ : ∀ {Σ X ar ar'} → Theory Σ X ar → Theory Σ X ar' → Set
_⇒T_ T₁ T₂ = ∀ {s} {ax} → ax ∈ T₂ → T₁ ⊢ ax
\end{spec}

\noindent If we have that a theory $T_1$ implies another theory
$T_2$, then for any model $\mathcal{A}$ of $T_1$, $\mathcal{A}$ is
model of $T_2$. The proof is direct by correctness: Let $e \in T_2$,
then we have $T_1 \vdash (\forall X)\, e$, and because of correctness
we have $\mathcal{A} \models e$.

\begin{spec}
⊨T⇒ : ∀  {Σ X ar ar'} → (T₁ : Theory Σ X ar) (T₂ : Theory Σ X ar')
         (p⇒ : T₁ ⇒T T₂) → (A : Algebra Σ) → A ⊨T T₁ → A ⊨T T₂
⊨T⇒ T₁ T₂ p⇒ A satAll = λ ax → correctness (p⇒ ax) A satAll
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

