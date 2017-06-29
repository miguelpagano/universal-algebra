\section{Morphisms between signatures}
\label{sec:trans}
The propositional calculus of Dijkstra and Scholten \cite{dijkstra-scholten} is an alternative
boolean theory whose only non-constants operation are equivalence and
disjunction. 
\begin{spec}
data bool-ops' : List ⊤ × ⊤ → Set where
  f' t'    : bool-ops' ([] ↦ tt)
  equiv' or' : bool-ops' (([ tt , tt ]) ↦ tt)

bool-sig' : Signature
bool-sig' = record { sorts = ⊤ , ops = bool-ops' }
\end{spec}
It is clear that one can translate recursively any term over
|bool-sig| to a term in |bool-sig'| preserving its
semantics. % Tiene sentido decir cómo?
An alternative and more general way is to specify how to translate
each operation in |bool-sig| using operations in |bool-sig'|. In this way,
any |bool-sig'|-algebra can be seen as a |bool-sig|-algebra: a
|bool-sig|-operation |f| is interpreted as the semantics of the
translation of |f|. In particular, the translation of formulas is
recovered as the initial homomorphism between |∣T∣ bool-sig| and the
transformation of |∣T∣ bool-sig'|. In this section we formalize the
concepts of \emph{derived signature morphism} and \emph{reduct
  algebra} as introduced, for example, by Sanella et al.~\cite{sannella2012foundations}.

\subsection{Derived signature morphism}

Although the disjunction from |bool-sig| can be directly mapped to its
namesake in |bool-sig'|, there is no unary operation in |bool-sig'| to
translate the negation. In fact, we should be able to translate an
operation as a combination of operations in |bool-sig'| and
also refer to the arguments of the original operation.
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
translation. Notice that |bool-sig| and |bool-sig'| share the sorts; in
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
  ops↝ : ∀  {ar s} → (f : bool-ops (ar ↦ s)) → map id ar ⊩ s
  ops↝ neg  = equiv' ∣$∣ ⟨⟨ # zero , f' ∣$∣ ⟨⟩ ⟩⟩
  ops↝ and  = equiv' ∣$∣ ⟨⟨ equiv' ∣$∣ ⟨⟨ p , q ⟩⟩ , or' ∣$∣ ⟨⟨ p , q ⟩⟩ ⟩⟩
    where  p = # zero
           q = # (suc zero)
\end{spec}
\subsection{Transformation of Algebras}
\newcommand{\intSign}[2]{#1 \hookrightarrow #2}
\newcommand{\intTheo}[1]{\widetilde{\theory{#1}}}
\newcommand{\algTrans}[1]{\langle \mathcal{#1} \rangle}
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
the functor on algebras: the interpretation of a $\Sigma_s$-sort $s$ is given by
  $\algTrans{A}_s = \mathcal{A}_{(\mapSort{m}{s})}$ and 
for interpreting an operation $f$ in the reduct algebra
$\algTrans A$ we use the interpretation of the formal term $m f$, which
is recursively defined by
\begin{spec}
  ⟦_⟧ₜ : ∀ {ar s} → ar ⊩ s → ∥ A ⟦ ar ⟧ₛ* ∥ → ∥ A ⟦ s ⟧ₛ ∥
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

\newcommand{\theory}[1]{\ensuremath{\mathit{E}_{#1}}}

\subsection{Translation of theories} From a signature morphism
$m : \intSign{\Sigma_s}{\Sigma_t}$ one gets the translation of ground
|Σₛ| terms as the initial homomorphism from |T Σₛ| to |⟨ T Σₜ ⟩|. With
an appropriate extension to variables, this translation applied to a
theory $\theory{s}$ over $\Sigma_s$ yields the theory $\intTheo{s}$
over $\Sigma_t$. Moreover if $\mathcal{A}_t\models\intTheo{s}$, one
would think that the reduct $\langle \mathcal{A}_t \rangle$ is a model
of the original theory, \ie
$\langle \mathcal{A}_t \rangle \models \theory{s}$. Even better, if
$\theory{t}$ is a stronger theory than the translated theory
$\intTheo{s}$ and if $\mathcal{A}_t$ is a model for $\theory{t}$, we
would like that the reduct algebra models $\theory{s}$. In Agda such a
result would be realized as a function |⊨↝| with the following type:
\begin{spec}
 ⊨↝ : ∀ Aₜ Eₜ Eₛ → Aₜ ⊨ₘ Eₜ → (Eₜ ⊢ ↝* Eₛ ) → 〈 Aₜ 〉 ⊨ₘ Eₛ
\end{spec}

With the morphism $m : \intSign{\Sigma_s}{\Sigma_t}$, one can define
the translation of open terms from |T Σₛ 〔 Xₛ 〕| to |T Σₜ 〔 Xₜ 〕|
using initiality if we also have a renaming function |↝ᵥ : {s : sorts
  Σₛ} → Xₛ s → Xₜ (m ↝ₛ s)|. In general, however, we cannot prove the
\emph{satisfaction property}: if a $\Sigma_t$-algebra models the
translation of an equation, then its reduct models the original
equation. The technical issue is the impossibility of defining a
$\Sigma_t$-environment from a $\Sigma_s$-environment. There is a
well-known solution which consists on restricting the set of variable
of the target signature by letting
$X_t = \bigcup_{s \in \Sigma_s , t = m \hookrightarrow s} X_s$.  Under
this restriction, we can prove the satisfaction property and
furthermore define the function |⊨↝|. We feel that such a restriction
over the set of variables is somewhat inconvenient to use in practice,
but it can be alleviated if the original variables of $\theory{t}$ are
included in the calculated set of variables.

% \paragraph{Implication of translated theories.}
% From a signature translation $t : \intSign{\Sigma_s}{\Sigma_t}$, we
% can think how to relate theories $Th_s$ and $Th_t$ of each signature
% respectively.

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

