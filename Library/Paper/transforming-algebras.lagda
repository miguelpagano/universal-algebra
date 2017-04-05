\section{Signature translation}
\label{sec:trans}

Let us consider the example of the previous section. We defined a
signature |Σbool₁| for a boolean logic, with negation, conjuction and
disjunction. There are other theories for boolean logic, with another
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
Dijkstra-Scholten and it is proved equivalent to the theory of previous
section in \cite{rocha-bool} (where are called $T_{Bool}$ and $T_{DS}$).
We could translate any formula in the language
described by |Σbool₁| to a formula in |Σbool₂|. Constants and operator
$\vee$ are mapped identically, and for $\neg$ and $\wedge$ we want
to translate a term $\neg P$ to $P \equiv False$, and a term
$P \wedge Q$ to $(P \equiv Q) \equiv P \vee Q$. Instead of simply
defining a function from terms in |Σbool₁| to terms in |Σbool₂|, we could do
something more general, specifying
how to interpret each operation in |Σbool₁| using operations in |Σbool₂|. In this
way, if we have a |Σbool₂|-algebra (i.e., we have interpretations for each
operation in |Σbool₂|) we could transform it in a |Σbool₁|-algebra: For each
|Σbool₁|-operation, we use the translation to |Σbool₂|-operations, and then we
have how to interpret them.
In particular, the function mapping terms in |Σbool₁| to terms in
|Σbool₂| will be the initial homomorphism between |∣T∣ Σbool₁| and the transformation of |∣T∣ Σbool₂|.

In this section we proceed to formalize the concepts of
\textit{derived signature morphism} and \textit{reduct algebra}, that
we call \textbf{signature translation} and \textbf{algebra transformation},
respectivelly.

\subsection{Signature translation}

If we want to give rules for interpreting operations in |Σbool₁| with
operations in |Σbool₂|, we note that is not simply a mapping between
operations. For example the \textit{negation} operator has to be interpreted
in |Σbool₂| combining the operations \textit{equivalence} and the constant
\textit{False} ($\neg P$ should be interpreted as $P \equiv False$).

We need to introduce a way to define rules for mapping operations in the
source signature, to meta-terms in the target signature, which will
be concretized when we interpret a concrete algebra. We call them
\textbf{formal terms}.

\newcommand{\sdash}[1]{\Vdash\!\!\!\!^{#1}}

\paragraph{Formal terms.}
We introduce a notion of \textit{formal terms},
relative to a signature, which are formal composition of identifiers
and operations. We introduce a typing system ensuring the
well-formedness of terms, where the contexts are arities,
\ie lists of sorts, and refer to variables by positions.
The typing rules for formal terms are:
\manu{Cambié el nombre de ``variables'' de formal terms por el
  de identificadores, para que no se confunda con las variables
  del cálculo ecuacional.}

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
define the next |Σbool₂|-formal term:

\begin{spec}
    op equiv₂ ⟨⟨ # zero , op f₂ ⟨⟩ ⟩⟩
\end{spec}

\noindent Because the operation |neg₁| is unary, we can to use
one identifier to define the corresponding formal term.
It consists of the application of |equiv₂| to the first identifier
and the constant |f₂|, i.e., the application of |f₂| to the empty
vector. 

We define a simpler notation for formal terms. We use |#_| for
the |ident| rule, and |_∣$∣_| for the |op| rule.

\paragraph{Signature translation.}
A \emph{signature translation} consists of two functions,
mapping sorts and operations:

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

$\intSign{\Sigma_s}{\Sigma_t}$ induces a transformation of
$\Sigma_t$-algebras as $\Sigma_s$-algebras; notice the contravariance
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
heterogeneous vectors. If the formal term is the identifier |n|, it's
corresponds to the element |n| of the vector |as|. If it is an
application of symbol |f| to formal terms |ts|, we apply the
interpretation of |f| to the interpretation of each term in |ts|.
Function |⟦_⟧⊩*| extends the definition above to vectors.

\paragraph{Algebra transformation.}
We can formalize the transformation of algebra in a direct way, however
the interpretation of operations is a little more complicated, since we need to convince Agda
that any vector |vs : VecH' (A ⟦_⟧ₛ ∘ ↝ₛ) is| has also the type
|VecH' A (map ↝ₛ is)|. This is accomplished with |reindex|.

\begin{spec}
 _⟨_⟩ₛ : ∀  {ℓ₀ ℓ₁} → (A : Algebra {ℓ₀} {ℓ₁} Σₜ) →
            (s : sorts Σₛ) → Setoid _ _
 A ⟨ s ⟩ₛ = A ⟦ ↝ₛ t s ⟧ₛ
\end{spec}
\begin{spec}
 _⟨_⟩ₒ :  ∀  {ℓ₀ ℓ₁ ar s} → (A : Algebra {ℓ₀} {ℓ₁} Σₜ) →
             ops Σₛ (ar ⇒ s) → (A ⟨_⟩ₛ) ✳ ar ⟶  A ⟨ s ⟩ₛ
 A ⟨ f ⟩ₒ = record  {  _⟨$⟩_ = ⟦ ↝ₒ t f ⟧⊩ ∘ reindex (↝ₛ t) 
                       ;  cong =  {!!} }
                                  
\end{spec}
\begin{spec}
 〈_〉 : Algebra Σₜ → Algebra Σₛ
 〈 A 〉 = 〈 A ⟨_⟩ₛ , (A ⟨_⟩ₒ) 〉
\end{spec}

Furthermore, we can also translate any homomorphism $h : \mathcal{A}
\to \mathcal{A'}$ to a homomorphism $\widetilde{h} :
\widetilde{\mathcal{A}} \to \widetilde{\mathcal{A'}}$:

\begin{spec}
   〈_〉ₕ : Homo A A' → Homo 〈 A 〉 〈 A' 〉
   〈 h 〉ₕ = record  { ′_′ = ′ h ′ ∘ ↝ₛ t ; cond = {!!} }
\end{spec}

With the signature translation |Σtrans : Σbool₁ ↝ Σbool₂| we can
transform any |Σbool₂|-algebra to a |Σbool₁|-algebra and the same
with the homomorphisms. Let us consider a |Σbool₂|-algebra Bool₂:

\begin{spec}
Bool₂ : Algebra Σbool₂
Bool₂ = BCarrier ∥ Bops
  where BCarrier = λ _ → setoid Bool
        Bops : ∀  {ar s} → (f : ops Σbool₂ (ar , s)) →
                  BCarrier ✳ ar ⟶ BCarrier s
        Bops = {!!}
\end{spec}

\noindent where |Bops| is the interpretation of each |Σbool₂|-operation
in the setoid of the type |Bool| from the standard library.

We can see |Bool₂| as a |Σbool₁|-algebra, i.e., we can obtain for
free the interpretation of each operation in |Σbool₁| in the setoid
|Bool|:

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
Because the \textit{freeness} property, we have an unique homomorphism
from the $\Sigma_s$-algebra |T Σₛ 〔 Xₛ 〕| to any other extending an
environment. In particular
we can obtain the homomorphism to the algebra |T Σₜ 〔 Xₜ 〕|
transformed via $t$, where the environment extended consists of assign to
each variable $v \in X_s\;s$ the term $tvars\;v \in X_t (t\,s)$.
Thus, we get for free a function mapping |Σₛ 〔 Xₛ 〕|-terms to |Σₜ 〔 Xₜ 〕|-terms:

\begin{spec}
  term↝ : Homo (T Σₛ 〔 Xₛ 〕) 〈 T Σₜ 〔 Xₜ 〕 〉
  term↝ = TΣXHom 〈 T Σₜ 〔 Xₜ 〕 〉 θv
    where θv : Env Xₛ 〈 T Σₜ 〔 Xₜ 〕 〉
          θv v = term (inj₂ (tvars v)) ⟨⟩
          open InitHomoExt 〈 T Σₜ 〔 Xₜ 〕 〉 θv
\end{spec}


