\section{Signature translation}
\label{sec:trans}

Let us consider the example of the previous section. We defined a
signature |Σbool₁| for boolean algebras, with complementation, meet and
join. There are other theories for boolean logic, with another
operators. For example, consider the boolean logic consisting
of constants True and False, and operators for disjunction and
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

\noindent This signature corresponds to the propositional logic of
Dijkstra-Scholten and it is proved to be equivalent to the theory of previous
section in \cite{rocha-bool}. % (where are called $T_{Bool}$ and $T_{DS}$).
It is clear that we could translate any formula in the language
described by |Σbool₁| to a formula in |Σbool₂|. The constants and the join operator
 are mapped to their name-sake;  $\neg$ and $\wedge$ should be translated
differently, for instance, the term $\neg P$ should be mapped to $P \equiv False$, and a term
$P \wedge Q$ to $(P \equiv Q) \equiv P \vee Q$. Instead of simply
defining a function from terms in |Σbool₁| to terms in |Σbool₂|, we can do
something more general, specifying
how to interpret each operation in |Σbool₁| using operations in |Σbool₂|. In this
way, if we have a |Σbool₂|-algebra (i.e., we have interpretations for each
operation in |Σbool₂|) we can transform it in a |Σbool₁|-algebra; indeed, for each
|Σbool₁|-operation, we use the translation to |Σbool₂|-operations, and then we
 interpret this translated term.
In particular, the function mapping terms in |Σbool₁| to terms in
|Σbool₂| will be the initial homomorphism between |∣T∣ Σbool₁| and the transformation of |∣T∣ Σbool₂|.

In this section we proceed to formalize the concepts of
\textit{derived signature morphism} and \textit{reduct algebra}, which we will
 call \textbf{signature translation} and \textbf{algebra transformation},
respectively.

\subsection{Signature translation}

If we want to give rules for interpreting operations in |Σbool₁| with
operations in |Σbool₂|, we note that is not simply a mapping between
operations. For example the \textit{negation} operator has to be interpreted
in |Σbool₂| by combining the operations \textit{equivalence} and the constant
\textit{False}. % ($\neg P$ should be interpreted as $P \equiv False$).

There is a need to have a way to define rules for mapping operations
in the source signature, to meta-terms in the target signature. We
call them \textbf{formal terms}.

\newcommand{\sdash}[1]{\Vdash\!\!\!\!^{#1}}

\paragraph{Formal terms.}
We introduce a notion of \textit{formal terms},
relative to a signature, which are formal composition of identifiers
and operations. We introduce a typing system ensuring the
well-formedness of terms, where the contexts are arities,
\ie lists of sorts, and refer to variables by positions.
The typing rules for formal terms are:

\begin{gather*}
\inferrule[(ident)]{ }{[s_{1},\ldots,s_{n}] \sdash{\Sigma} \sharp i : s_i}\\
\inferrule[(op)]{f : [s_1,...,s_{n}] \Rightarrow_{\Sigma} s\ \ \ 
  \mathit{ar} \sdash{\Sigma} t_1 : s_1\ \cdots\ \ \ 
  \mathit{ar} \sdash{\Sigma} t_{n} : s_{n} }
{\mathit{ar} \sdash{\Sigma} f\,(t_1,...,t_{n}) : s}
\end{gather*}
This typing system can be formalized as an inductive family
parameterized by arities and indexed by sorts. 

\begin{spec}
 data _⊩_  (ar' : Arity Σ) : (sorts Σ) → Set where
   ident  : (n : Fin (length ar')) → ar' ⊩ (ar' ‼ n)
   op     : ∀ {ar s} → ops Σ (ar ⇒ s) → HVec (ar' ⊩_) ar → ar' ⊩ s
\end{spec}

\noindent A formal term specifies the way to interpret an operation
from a source signature in the target signature. The arity |ar'|
corresponds to the sorts of the identifiers that are posible to use
in a rule. For example if we want to interpret the negation operator
from signature |Σbool₁| in the signature |Σbool₂| we can
define the following |Σbool₂|-formal term:
\begin{spec}
    op equiv₂ ⟨⟨ # zero , op f₂ ⟨⟩ ⟩⟩
\end{spec}

\noindent Because the operation |neg₁| is unary, we can use one
identifier to define the corresponding formal term.  It consists of
the application of |equiv₂| to the first identifier and the constant
|f₂|, i.e., the application of |f₂| to the empty vector.  Henceforth,
we use a simpler notation for formal terms: |#_| stands for the
|ident| rule and |_∣$∣_|, for the |op| rule.

\paragraph{Signature translation.}
A \emph{signature translation} consists of two functions,
mapping sorts and operations, respectively:

\begin{spec}
record _↝_ (Σₛ Σₜ : Signature) : Set where
 field
  ↝ₛ : sorts Σₛ → sorts Σₜ
  ↝ₒ : ∀ {ar s} → ops Σₛ (ar , s) → map ↝ₛ ar ⊢ ↝ₛ s
\end{spec}

\noindent Let us see a translation from |Σbool₁| to |Σbool₂|:

\begin{spec}
  ops↝ : ∀  {ar s} → (f : Σops₁ (ar ↦ s)) → lmap id ar ⊩ s
  ops↝ t₁    = t₂ ∣$∣ ⟨⟩
  ops↝ f₁    = f₂ ∣$∣ ⟨⟩
  ops↝ or₁   = or₂ ∣$∣ ⟨⟨ # zero , # (suc zero) ⟩⟩ 
  ops↝ neg₁  = equiv₂ ∣$∣ ⟨⟨ # zero , f₂ ∣$∣ ⟨⟩ ⟩⟩
  ops↝ and₁  = equiv₂ ∣$∣ ⟨⟨ equiv₂ ∣$∣ ⟨⟨ p , q ⟩⟩ , or₂ ∣$∣ ⟨⟨ p , q ⟩⟩ ⟩⟩
    where  p = # zero
           q = # (suc zero)

  Σtrans : Σbool₁ ↝ Σbool₂
  Σtrans = record { ↝ₛ = id ; ↝ₒ = ops↝ }
\end{spec}

\newcommand{\intSign}[2]{#1 \hookrightarrow #2}
\newcommand{\algTrans}[1]{\widetilde{\mathcal{#1}}}
\newcommand{\mapSort}[2]{#1\,#2}
\newcommand{\mapOp}[2]{#1\,#2}

\subsection{Transformation of Algebras}

A translation $\intSign{\Sigma_s}{\Sigma_t}$ induces a transformation of
$\Sigma_t$-algebras into $\Sigma_s$-algebras; notice the contravariance
of the transformation with respect to the signature translation. This is a
well-known concept in the theory of institutions and
\citet{sannella2012foundations} use the notion \textit{reduct algebra
with respect to a derived signature morphism} for a transformed algebra
induced by a signature translation.

Given a signature translation $t\,:\,\intSign{\Sigma_s}{\Sigma_t}$ and a
$\Sigma_t$-algebra $\mathcal{A}$, we denote with $\algTrans{A}$ its
transformation as a $\Sigma_s$-algebra. It is clear that every sort $s$
of $\Sigma_s$ can be interpreted via the interpretation of the translated sort:
$\algTrans{A} \llbracket s \rrbracket_s = \mathcal{A} \llbracket
\mapSort{t}{s} \rrbracket_s $.  The denotation of an operation $f$ is
obtained by the interpretation of the corresponding formal term:
$\algTrans{A} \llbracket f \rrbracket_o = \mathcal{A} \llbracket
\mapOp{t}{f}\, \rrbracket\!\!\Vdash $.

\paragraph{Interpreting formal terms.}
A formal term $\mathit{ar} \sdash{\Sigma} t : s$ can be interpreted
in a $\Sigma$-algebra |A| as a function from |⟦ ar ⟧ₛ*| to  |⟦ s ⟧ₛ|;

\begin{spec}
  ⟦_⟧⊩ : ∀ {ar s} → ar ⊩ s → A ⟦ ar ⟧ₛ* → ∥ A ⟦ s ⟧ₛ ∥
  ⟦ # n ⟧⊩       as =  as ‼v n
  ⟦ f ∣$∣ ts ⟧⊩  as = A ⟦ f ⟧ₒ ⟨$⟩ ⟦ ts ⟧⊩* as
\end{spec}

\noindent The function |_!!v_| is the indexing operator of
heterogeneous vectors. If the formal term is the identifier |n|, it
corresponds to the |n|-th element of the vector |as|. If it is an
application of the operation |f| to formal terms |ts|, we apply the
interpretation of |f| to the interpretation of each term in |ts|.
The function |⟦_⟧⊩*| extends |⟦_⟧⊩| to vectors.

\paragraph{Algebra transformation.}
We can formalize the transformation of algebra in a direct way, however
the interpretation of operations is a little more complicated, since we need to convince Agda
that any vector |vs : VecH' (A ⟦_⟧ₛ ∘ ↝ₛ) is| has also the type
|VecH' A (map ↝ₛ is)|, which is accomplished by |reindex|-ing the vector.
\begin{spec}
 _⟨_⟩ₛ : ∀  {ℓ₀ ℓ₁} → (A : Algebra {ℓ₀} {ℓ₁} Σₜ) →
            (s : sorts Σₛ) → Setoid _ _
 A ⟨ s ⟩ₛ = A ⟦ ↝ₛ t s ⟧ₛ

 _⟨_⟩ₒ :  ∀  {ℓ₀ ℓ₁ ar s} → (A : Algebra {ℓ₀} {ℓ₁} Σₜ) →
             ops Σₛ (ar ⇒ s) → (A ⟨_⟩ₛ) ✳ ar ⟶  A ⟨ s ⟩ₛ
 A ⟨ f ⟩ₒ = record  {  _⟨$⟩_ = ⟦ ↝ₒ t f ⟧⊩ ∘ reindex (↝ₛ t) 
                       ;  cong =  ?  }

 〈_〉 : Algebra Σₜ → Algebra Σₛ
 〈 A 〉 = 〈 A ⟨_⟩ₛ , (A ⟨_⟩ₒ) 〉
\end{spec}

Furthermore, we can also translate any homomorphism $h : \mathcal{A}
\to \mathcal{A'}$ to a homomorphism $\widetilde{h} :
\widetilde{\mathcal{A}} \to \widetilde{\mathcal{A'}}$:

\begin{spec}
   〈_〉ₕ : Homo A A' → Homo 〈 A 〉 〈 A' 〉
   〈 h 〉ₕ = record  { ′_′ = ′ h ′ ∘ ↝ₛ t ; cond = ? }
\end{spec}

With the signature translation |Σtrans : Σbool₁ ↝ Σbool₂| we can
transform any |Σbool₂|-algebra to a |Σbool₁|-algebra. Let us consider
the most natural |Σbool₂|-algebra Bool₂:

\begin{spec}
Bool₂ : Algebra Σbool₂
Bool₂ = record {_⟦_⟧ₛ = BCarrier ; _⟦_⟧ₒ = Bops }
  where BCarrier = λ _ → setoid Bool
        Bops : ∀  {ar s} → (f : ops Σbool₂ (ar , s)) →
                  BCarrier ✳ ar ⟶ BCarrier s
        Bops = ?
\end{spec}

\noindent where |Bops| is the interpretation of each |Σbool₂|-operation
by the correspoding meta-operation. We can see |Bool₂| as a |Σbool₁|-algebra, \ie we can obtain for
free the interpretation of each operation in |Σbool₁| in the setoid |Bool|:
\begin{spec}
Bool₁ : Algebra Σbool₁
Bool₁= 〈  B₂ 〉
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

