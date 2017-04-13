\section{Signature translation}
\label{sec:trans}
The propositional calculus of Dijkstra and Scholten \cite{dijkstra-scholten} is an alternative
boolean theory whose only non-constants operation are equivalence and
disjunction. 
\begin{spec}
data Σops' : List ⊤ × ⊤ → Set where
  f' t'    : Σops' ([] ↦ tt)
  iff' or' : Σops' (([ tt , tt ]) ↦ tt)

Σbool' : Signature
Σbool' = ⟨ ⊤ , Σops' ⟩
\end{spec}
It is clear that one can translate recursively any term over
|Σbool| to a term in |Σbool'| preserving its
semantics. % Tiene sentido decir cómo?
An alternative and more general way is to specify how to translate
each operation in |Σbool| using operations in |Σbool'|. In this way,
any |Σbool'|-algebra can be seen as a |Σbool|-algebra: a
|Σbool|-operation |f| is interpreted as the semantics of the
translation of |f|. In particular, the translation of formulas is
recovered as the initial homomorphism between |∣T∣ Σbool| and the
transformation of |∣T∣ Σbool'|. In this section we formalize the
concepts of \emph{derived signature morphism} and \emph{reduct
  algebra} as introduced, for example, by Sanella et al.~\cite{sannella2012foundations}.

\subsection{Derived signature translation}

Although the disjunction from |Σbool| can be directly mapped to its
namesake in |Σbool'|, there is no unary operation in |Σbool'| to
translate the negation. In fact, we should be able to translate an
operation as a combination of operations in |Σbool'| and
also a way to refer to the arguments of the original operation.
\newcommand{\sdash}[1]{\Vdash\!\!\!\!^{#1}}

We introduce the notion of \emph{formal terms} which are formal
composition of projections and operations. We introduce a type
system, shown in Fig.~\ref{fig:formalterms}, ensuring the
well-formedness of these terms: the contexts are arities, \ie lists of
sorts, and identifiers are pointers (like de Bruijn indices).
\begin{figure}[t]
  \centering
    \bottomAlignProof
    \AxiomC{}
    \RightLabel{\textsc{(prj)}}
    \UnaryInfC{$[s_{1},\ldots,s_{n}] \sdash{\Sigma} \sharp i : s_i$}
  \DisplayProof
% 
  \bottomAlignProof
  \insertBetweenHyps{\hskip -4pt}
  \AxiomC{$f : [s_1,...,s_{n}] \Rightarrow_{\Sigma} s$}
  \AxiomC{$\mathit{ar} \sdash{\Sigma} t_1 : s_1$}
  \AxiomC{$\cdots$}
  \AxiomC{$\mathit{ar} \sdash{\Sigma} t_n : s_n$}
  \RightLabel{\textsc{(op)}}
  \QuaternaryInfC{$\mathit{ar} \sdash{\Sigma} f\,(t_1,...,t_{n}) : s$}
  \DisplayProof
\caption{Type system for formal terms}
\label{fig:formalterms}
\end{figure}
It can be formalized as an inductive family
parameterized by arities and indexed by sorts. 
\begin{spec}
 data _⊩_  (ar' : Arity Σ) : (sorts Σ) → Set where
   #_     : (n : Fin (length ar')) → ar' ⊩ (ar' ‼ n)
   _∣$∣_    : ∀ {ar s} → ops Σ (ar ⇒ s) → HVec (ar' ⊩_) ar → ar' ⊩ s
\end{spec}
A formal term specifies how to interpret an operation from the source
signature in the target signature. The arity |ar'| specifies the sort
of each argument of the original operation. For example, since the
operation |neg| is unary, we can use one identifier when defining its
translation. Notice that |Σbool| and |Σbool'| share the sorts; in
general, one also consider a mapping between sorts.

A \emph{derived signature morphism} consists of a mapping between sorts
and a mapping from operations to formal terms:
\begin{spec}
record _↝_ (Σₛ Σₜ : Signature) : Set where
  field
    ↝ₛ : sorts Σₛ → sorts Σₜ
    ↝ₒ : ∀ {ar s} → ops Σₛ (ar , s) → (map ↝ₛ ar) ⊩ (↝ₛ s)
\end{spec}
\noindent We show the action of the morphism on the operations |neg| and |and|
\begin{spec}
  ops↝ : ∀  {ar s} → (f : Σops (ar ↦ s)) → map id ar ⊩ s
  ops↝ neg  = equiv' ∣$∣ ⟨⟨ # zero , f' ∣$∣ ⟨⟩ ⟩⟩
  ops↝ and  = equiv' ∣$∣ ⟨⟨ equiv' ∣$∣ ⟨⟨ p , q ⟩⟩ , or' ∣$∣ ⟨⟨ p , q ⟩⟩ ⟩⟩
    where  p = # zero
           q = # (suc zero)
\end{spec}
\subsection{Transformation of Algebras}
\newcommand{\intSign}[2]{#1 \hookrightarrow #2}
\newcommand{\algTrans}[1]{\widetilde{\mathcal{#1}}}
\newcommand{\mapSort}[2]{#1\,#2}
\newcommand{\mapOp}[2]{#1\,#2}

A signature morphism
$m\colon\intSign{\Sigma_s}{\Sigma_t}$ induces a functor from
$\Sigma_t$-algebras to
$\Sigma_s$-algebras.  Given a $\Sigma_t$-algebra
$\mathcal{A}$, we denote with
$\algTrans{A}$ the corresponding
$\Sigma_s$-algebra, which is known as the \emph{reduct algebra with
  respect to the morphism} $m$. Let us sketch the construction of
the functor on algebras: the interpretetion of a $\Sigma_s$-sort $s$ is given by
$\algTrans{A}_s = \mathcal{A}_{\mapSort{m}{s}}$ and 
for interpreting an operation $f$ in the reduct algebra
$\algTrans A$ we use the interpretation of the formal term $m f$, which
is recursively defined by
\begin{spec}
  ⟦_⟧ₜ : ∀ {ar s} → ar ⊩ s → A ⟦ ar ⟧ₛ* → ∥ A ⟦ s ⟧ₛ ∥
  ⟦ # n ⟧ₜ      as =  as ‼v n
  ⟦ f ∣$∣ ts ⟧ₜ  as = A ⟦ f ⟧ₒ ⟨$⟩ ⟦ ts ⟧ₜ* as
\end{spec}
\noindent Identifiers denote projections and the application of the
operation |f| to formal terms |ts| is interpreted as the interpretation of |f|
applied to the denotation of each term in |ts|, the function |⟦_⟧ₜ*| extends
|⟦_⟧ₜ| to vectors.

We can formalize the reduct algebra in a direct way,
however the interpretation of operations is a little more complicated,
since we need to convince Agda that any vector |vs : VecH' (A ⟦_⟧ₛ ∘
↝ₛ) is| has also the type |VecH' A (map ↝ₛ is)|, which is accomplished
by |reindex|-ing the vector.
\begin{spec}
module ReductAlg (m : Σₛ ↝ Σₜ) (A : Algebra Σₜ) where
  ⟨_⟩ₛ :  → (s : sorts Σₛ) → Setoid
  ⟨ s ⟩ₛ = A ⟦ ↝ₛ m s ⟧ₛ

  ⟨_⟩ₒ :  ∀ {ar s} → ops Σₛ (ar ⇒ s) → (⟨_⟩ₛ) ✳ ar ⟶  ⟨ s ⟩ₛ
  ⟨ f ⟩ₒ = record  {  _⟨$⟩_ = ⟦ ↝ₒ m f ⟧ₜ ∘ reindex (↝ₛ m) ;  cong =  ?  }

  _〈_〉 : Algebra Σₛ
  _〈_〉 = 〈 ⟨_⟩ₛ , ⟨_⟩ₒ 〉
\end{spec}

The action of the functor on homomorphism is also straightforward: 
\begin{spec}
module ReductHomo {m : Σₛ ↝ Σₜ} {A A'} (H : Homo {Σₜ} A A')  where
   〈_〉ₕ : Homo (m 〈 A 〉) (m 〈 A' 〉)
   〈 h 〉ₕ = record  { ′_′ = ′ h ′ ∘ ↝ₛ m ; cond = ? }
\end{spec}

\subsection{Translation of theories}
Given a signature translation $t : \intSign{\Sigma_s}{\Sigma_t}$, two
families $X_s$ and $X_t$ of variables indexed by the respective
sorts, a function $tvars : X_s s \rightarrow X_t (t s)$,
for each sort $s$ of $\Sigma_s$ and tow theories
$\Sigma_t$-theory $Th_t$ and a $\Sigma_s$-theory $Th_s$, we say that
$Th_t$ implies $Th_s$ if for each axiom $e \in Th_s$, there exists
a proof of the translation of $e$ in $Th_t$.

Let us define the translation of $\Sigma_s$-terms extended to $X_s$ to
$\Sigma_t$-terms extended to $X_t$.

\paragraph{Terms translation.}
Because of the \textit{freeness} property, we have an unique homomorphism
from the $\Sigma_s$-algebra |T Σₛ 〔 Xₛ 〕| to any other algebra extended with an
environment. In particular
we can obtain the homomorphism to the algebra |T Σₜ 〔 Xₜ 〕|
transformed via $t$, where the environment consists of mapping 
each variable $v \in X_s\;s$ to the term $tvars\;v \in X_t (t\,s)$.
Thus, we get for free a function mapping |Σₛ 〔 Xₛ 〕|-terms to |Σₜ 〔 Xₜ 〕|-terms:

\begin{spec}
  term↝ : Homo (T Σₛ 〔 Xₛ 〕) 〈 T Σₜ 〔 Xₜ 〕 〉
  term↝ = TΣXHom (Σₜ 〔 Xₜ 〕) 〈 T Σₜ 〔 Xₜ 〕 〉 θv
    where θv : Env Xₛ 〈 T Σₜ 〔 Xₜ 〕 〉
          θv v = term (inj₂ (tvars v)) ⟨⟩
\end{spec}

\noindent It's straightforward to extend this definition to equations,
we call |eq↝| to this extension.

% \paragraph{Implication of translated theories.}
% From a signature translation $t : \intSign{\Sigma_s}{\Sigma_t}$, we
% can think how to relate theories $Th_s$ and $Th_t$ of each signature
% respectivelly.

% A first interesting definition is the translation of a
% $\Sigma_s$-theory. It means, to translate each $\Sigma_s$-equation, and
% we need to translate variables. Under some restrictions over the
% translation $t$, we can construct a set of variables $X_t$ in $\Sigma_t$ and
% we can define the mapping of variables: $X_s \rightarrow X_t$. Then
% we can define the translation of theories:

% \begin{spec}
% 〈_〉T : ∀ {ar} → (Thₛ : Theory Σₛ Xₛ ar) → Theory Σₜ Xₜ (lmap (↝ₛ Σ↝) ar)
% \end{spec}

% Other interesting definition is to say when $Th_t$ implies $Th_s$:

% \begin{spec}
% Thₜ ⇒T~ Thₛ = ∀ {s} {ax : Equation Σₛ Xₛ s} → ax ∈ Thₛ → Thₜ ⊢ eq↝ ax
% \end{spec}

% \noindent Again we need to translate variables.

% In both cases, under restrictions, we can prove that models of $Th_t$ are
% models of $Th_s$, and we can enunciate this preservation of models in
% this way:
% \medskip

% \textit{Model preservation from a translated theory:}

% \begin{spec}
% ⊨T↝ : ∀ {ar} → (A : Algebra Σₜ) → A ⊨T 〈 Tₛ 〉T → 〈 A 〉 ⊨T Tₛ
% \end{spec}

% \textit{Model preservation from a implicated theory:}

% \begin{spec}
% ⊨T↝ : Thₜ ⇒T~ Thₛ → (A : Algebra Σₜ) → A ⊨T Thₜ → 〈 A 〉 ⊨T Thₛ
% \end{spec}

