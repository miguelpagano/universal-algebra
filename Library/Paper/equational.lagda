\section{Equational Logic}

With the development of the previous section, we proceed to
formalize Equational Logic in Agda.

\subsection{Variables, environments and substitution}

\paragraph{Variables} A signature $\Sigma$ as we defined consists of sorts and operation
symbols. We can add variables of each sort and construct a new
signature, consisting of the same operations than $\Sigma$, but
adding new constant symbols, one for each variable:

\begin{spec}
  Vars : (Σ : Signature) → Set₁
  Vars Σ = (s : sorts Σ) → Set

  _〔_〕 : (Σ : Signature) → (X : Vars Σ) → Signature
  Σ 〔 X 〕 = record  { sorts = sorts Σ
                      ; ops =  λ { ([] , s) → ops Σ ([] , s) ⊎ X s
                                 ; ty → ops Σ ty
                               }
                      }
\end{spec}

We define variables as a family indexed by sorts of |Σ|, and
the new signature |Σ 〔 X 〕| is defined with the disjoint union
from standard
library. For each sort, constants symbols are divided in the
two injections. The first one contains the original constant
symbols of sort |s|, and the second
one contains the variables of sort |s|. Note the benefit of having
defined operations with a family indexed by arities. We can refer
to constants symbols in a simple way.

In the literature is used the term \textit{ground signature} for
signatures consisting only of constant symbols. And a signature
with variables is constructed via the union of a signature and a
ground signature.

From a signature |Σ| and a family of variables |X|, we can
form a |Σ|-algebra with the terms of the term algebra of
|Σ 〔 X 〕|, forgetting the variables:

\begin{spec}
T_〔_〕 : (Σ : Signature) → (X : Vars Σ) → Algebra Σ
T Σ 〔 X 〕  = (λ s → ∣T∣ ⟦ s ⟧ₛ)
             ∥ (λ  { {[]} {s} f       → ∣T∣ ⟦ inj₁ f ⟧ₒ
                   ; {s₀ ∷ ar} {s} f  → ∣T∣ ⟦ f ⟧ₒ })
  where open TermAlgebra (Σ 〔 X 〕)
\end{spec}

\paragraph{Environments}
Given a $\Sigma$-algebra $\mathcal{A}$ and a family of variables
$X$, we can define the set of environments from $X$ to
$\mathcal{A}$. Each variable of sort $s$ is mapped to an element
in the interpretation of $s$ in $\mathcal{A}$:

\begin{spec}
Env : ∀ {Σ} {X} → (A : Algebra Σ) → Set _
Env {Σ} {X} A = ∀ {s} → X s → ∥ A ⟦ s ⟧ₛ ∥
\end{spec}

\noindent Given a environment |θ : Env {X = X} A|, it's
straightforward extending it to terms. We write this extension
with |(θ ↪)|.

\paragraph{Substitutions}

A substitution of variables to terms is simply an environment
of the term algebra |T Σ 〔 X 〕|. If |σ| is a substitution, we
write the extension to terms with |σ ↪s|.

\begin{spec}
  Subst : Set
  Subst = Env {X = X} (T Σ 〔 X 〕)

  _↪s : Subst → {s} → ∥ ∣T∣ ⟦ s ⟧ₛ ∥ → ∥ ∣T∣ ⟦ s ⟧ₛ ∥
  _↪s σ t = (σ ↪) t
\end{spec}
  
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

A \textbf{theory} consist of a signature and a set of equations.
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

We say that $\mathcal{A}$ satisfies a theory $T$ if satisfies each
equation in $T$.

\begin{spec}
record  ⊨T {Σ X ar} (E : Theory Σ X ar) (A : Algebra Σ) : Set _ where
  field
    satAll : ∀ {s} {e : Equation Σ X s} → e ∈ E → A ⊨ e
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

We conclude the formalization of equational logic with proofs of
correctness and completeness.

\paragraph{Correctness.} If an equation $e$ is provable in a theory
$T$, then for all $\Sigma$-algebra $\mathcal{A}$ that satisfies the
axioms in $T$, $\mathcal{A}$ satisfies $e$.

\begin{spec}
  correctness :  ∀ {Σ X} {ar} {s} {T : Theory Σ X ar} {e : Equation Σ X s}
                 → T ⊢ e → (A : Algebra Σ) → ⊨T E A → A ⊨ e
  correctness : ...
\end{spec}

\paragraph{Completeness.} 
If all $\Sigma$-algebra $\mathcal{A}$ that satisfies the axioms in $T$,
$\mathcal{A}$ satisfies an equation $e$, then $e$ is provably in $T$.

\begin{spec}
complete : ∀ {Σ X} {ar : Arity Σ} {s : sorts Σ} {E : Theory Σ X ar}
{e : Equation Σ X s} → ((A : Algebra Σ) → ⊨T E A → A ⊨ e) → E ⊢ e
complete = ...
\end{spec}

\manu{Ver qué podemos decir de esas pruebas. Quizás contar la idea de
la prueba de completitud.}

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

