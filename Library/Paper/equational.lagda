\section{Equational Logic}

In this section we formalize (conditional) equational logic, for this
we extend the term algebra with variables and introduce a formal
system for conditional equations; we show that this system is sound a
complete. 

%\subsection{Variables, environments and substitution}
\subsection{Free algebra with variables}
The first step to define equations is to add variables to the set of
terms. Given a signature |Σ|, we say that |X : sorts Σ → Set| is a
family of variables for |Σ|, we let |Vars Σ = sorts Σ → Set|. For each
family |X : Vars Σ| we enlarge the signature by taking the variables as
new constants (\ie, operations with arity |[]|).
% \paragraph{Variables} A signature $\Sigma$ consists of sorts and operation
% symbols. We can add variables of each sort and construct a new
% signature, consisting of the same operations than $\Sigma$, but
% adding new constant symbols, one for each variable:
\begin{spec}
  _〔_〕 : (Σ : Signature) → (X : Vars Σ) → Signature
  Σ 〔 X 〕 = record  { sorts = sorts Σ ; ops =  ops' }
     where   ops' ([] , s)   = ops Σ ([] , s) ⊎ X s
             ops' (ar , s)   = ops Σ (ar , s)
\end{spec}%
% We define variables as a family indexed by sorts of |Σ|, and
% the new signature |Σ 〔 X 〕| is defined with the disjoint union
% from standard
% library. For each sort, constants symbols are divided in the
% two injections. The first one contains the original constant
% symbols of sort |s|, and the second
% one contains the variables of sort |s|. Note the benefit of having
% defined operations with a family indexed by arities. We can refer
% to constants symbols in a simple way.
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
Since any |Σ 〔 X 〕|-algebra can be seen in this way, from the
initiality of |T Σ 〔 X 〕| we deduce that it enjoys the universal
\textit{freeness} property: Given a $\Sigma$-algebra $\mathcal{A}$,
and an environment $\theta$, there exists an unique homomorphism $h$
from |T Σ 〔 X 〕| to $\mathcal{A}$ such that $h(x) = \theta(x)$ for
all variable $x$.

% A substitution of variables to terms is simply an environment
% of the term algebra |∣T∣ Σ 〔 X 〕|. 

% \begin{spec}
%   Subst : Set
%   Subst = Env X (T Σ 〔 X 〕)
% \end{spec}

\subsection{Equations, satisfactibility and provability}

\paragraph{Equations}
A $\Sigma$-equation consists of a family of variables $X$,
two $\Sigma(X)$-terms of the same sort $t$ and $t'$, and a
(possibly empty) set of pairs of $\Sigma(X)$-terms $u_i , u'_i$
each of the same sort. In \cite{goguen-equational} an equation
is writen in the form $(\forall X) t = t' \,\text{if}\, u_1=u'_1,...,
u_n=u'_n$.
We define equation in Agda with a record parameterized on a
signature, a family of variables and a sort:

\begin{spec}
record Equation (Σ : Signature) (X : Vars Σ) (s : sorts Σ) : Set where
  constructor ⋀_≈_if「_」_
  field
    left  : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥
    right : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥
    carty : Arity Σ
    cond :  HVec (λ s' → ∥ ∣T∣ (Σ 〔 X 〕) ⟦ s' ⟧ₛ ∥) carty ×
            HVec (λ s' → ∥ ∣T∣ (Σ 〔 X 〕) ⟦ s' ⟧ₛ ∥) carty
\end{spec}

\noindent The two terms of the equation are fields |left|
and |right|. If the equation is conditional, we have a non-empty
arity |carty| and two vectors of terms with arity |carty|.

We can give a short notation for non-conditional equations:

\begin{spec}
⋀_≈_ : ∀ {Σ X s} → (t t' : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥) → Equation Σ X s
⋀ t ≈ t' = ⋀ t ≈ t' if「 [] 」 (⟨⟩ , ⟨⟩)
\end{spec}

A \textbf{theory} consists of a signature and a set of equations.
The type of heterogeneous vectors is appropiate to formalize the
set of equations, possibly of different sorts. Thus, a theory is
defined as a vector of equations of a signature $\Sigma$ and a set
of variables $X$:

\begin{spec}
Theory : (Σ : Signature) → (X : Vars Σ) → (ar : Arity Σ) → Set
Theory Σ X ar = HVec (Equation Σ X) ar
\end{spec}

\paragraph{Satisfactibility.}
Given a $\Sigma$-equation $e \doteq (\forall X) t = t' \,\text{if}\,
u_1=u'_1,..., u_n=u'_n$ and a $\Sigma$-algebra $\mathcal{A}$,
$\mathcal{A}$ \textbf{satisfies} $e$, writen $A \models e$, iff
for any environment $\theta$, if $\theta(u_i)=\theta(u'_i)$, for
$1 \leq i \leq n$, then $\theta(t)=\theta(t')$.

We formalize this definition using the extension of a relation to
vectors. Each condition $\theta(u_i)=\theta(u'_i)$, where $u_i$ and
$u'_i$ are terms of sort $s_i$, is an element of
the extension to vectors of the equality of the carrier of $s_i$.

\begin{spec}
_⊨_ : ∀ {Σ X s} → (A : Algebra Σ) → Equation Σ X s → Set _
_⊨_ A  (⋀ t ≈ t' if「 _ 」 (us , us')) =
       (θ : Env A) → _∼v_ {R = λ _ uᵢ uᵢ' → ((θ ↪) uᵢ) ≈ᵢ ((θ ↪) uᵢ')} us us' →
       ((θ ↪) t) ≈ₛ ((θ ↪) t')
\end{spec}

\noindent where |_≈ᵢ_| and |_≈ₛ_| are the corresponding equivalence
relations of each sort.

We say that $\mathcal{A}$ satisfies a theory $T$ if it satisfies each
equation in $T$ (we say that $\mathcal{A}$ is \textit{a model} of
$T$).

\begin{spec}
_⊨T_ : ∀ {Σ X ar} → (A : Algebra Σ) → (E : Theory Σ X ar) → Set _
A ⊨T E = ∀ {e} → e ∈ E → A ⊨ e
\end{spec}

\noindent Type |_∈_| formalizes the relation of membership in vectors.

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

