\section{Signature translation}
\label{sec:trans}

Let us consider the example of the previous section. We defined a
signature |Σbool₁| for a boolean logic, with negation, conjuction and
disjunction. There are other theories for boolean logic, with another
operators. For example, consider the another boolean logic consisting
of constants True y False, and operators for disjunction and
equivalence. We can give a signature |Σbool₂|:

\begin{spec}
data Σops₂ : List ⊤ × ⊤ → Set where
  t₂     : Σops₂ ([] ↦ tt)
  f₂     : Σops₂ ([] ↦ tt)
  or₂    : Σops₂ ((tt ∷ [ tt ]) ↦ tt)
  equiv₂ : Σops₂ ((tt ∷ [ tt ]) ↦ tt)


Σbool₂ : Signature
Σbool₂ = ⟨ ⊤ , Σops₂ ⟩
\end{spec}

\noindent This signature corresponds to the boolean theory $T_{DS}$ in
\cite{rocha-bool}. We could translate any formula in the language
described by |Σbool₁| to a formula in |Σbool₂|. Constants and operator
$\vee$ are mapped identically, and for $\neg$ and $\wedge$ we want
to translate a term $\neg P$ to $P \equiv False$, and a term
$P \wedge Q$ to $(P \equiv Q) \equiv P \vee Q$. Let us note that
this mapping is not simply replace one operation by another. We need
to define a rule that allows to translate any formula in the first
language to another in the second. 

\subsection{Signature translation}

In order to give a formalization of this kind of translations, we
introduce the concept of \textit{signature translation}, that
corresponds to \textit{derived signature morphism} in some literature.
(\manu{buscar referencia}).

\newcommand{\sdash}[1]{\vdash\!\!\!\!^{#1}}

\paragraph{Formal terms.}
We introduce a notion of \textit{formal terms},
relative to a signature, which are formal composition of variables and
operations. We introduce a typing system ensuring the well-formedness
of terms, where the contexts are arities, \ie lists of sorts, and
refer to variables by positions. The typing rules for formal terms
are:
\begin{gather*}
\inferrule[(var)]{ }{[s_{1},\ldots,s_{n}] \sdash{\Sigma} \sharp i : s_i}\\
\inferrule[(op)]{f : [s_1,...,s_{n}] \Rightarrow_{\Sigma} s\ \ \ 
  \mathit{ar} \sdash{\Sigma} t_1 : s_1\ \cdots\ \ \ 
  \mathit{ar} \sdash{\Sigma} t_{n} : s_{n} }
{\mathit{ar} \sdash{\Sigma} f\,(t_1,...,t_{n}) : s}
\end{gather*}
This typing system can be formalized as an inductive family parameterized
by arities and indexed by sorts. 

\begin{spec}
 data _⊢_  (ar' : Arity Σ) : (sorts Σ) → Set where
   var  : (n : Fin (length ar')) → ar' ⊢ (ar' ‼ n)
   op   : ∀ {ar s} → ops Σ (ar ⇒ s) → HVec (ar' ⊢_) ar → ar' ⊢ s
\end{spec}
\manu{cambiar símbolo para los formal terms, es el mismo que para
      las pruebas ecuacionales.}

\paragraph{Signature translation.}
A \emph{signature translation} consists of two functions,
mapping sorts and operations:

\begin{spec}
record _↝_ (Σₛ Σₜ : Signature) : Set where
 field
  ↝ₛ : sorts Σₛ → sorts Σₜ
  ↝ₒ : ∀ {ar s} → ops Σₛ (ar , s) → map ↝ₛ ar ⊢ ↝ₛ s
\end{spec}

\newcommand{\intSign}[2]{#1 \hookrightarrow #2}
\newcommand{\algTrans}[1]{\widetilde{\mathcal{#1}}}

\subsection{Algebra transformation}

