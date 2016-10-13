%if False
\begin{code}
module transforming-algebras where
open import univ-alg
\end{code}
%endif
\section{Algebra transformation}
\label{sec:trans}

With the formalization thus far, one can define source and target
languages from signatures $\Sigma_s$ and $\Sigma_t$, obtaining
their respective term algebras.

In our example, the source language is given by the
term algebra of the signature $\Sigma_e$ and, parallely, the target 
language is the term algebra of the following signature:
\begin{code}
data Sortsₘ : Set where C : Sortsₘ

data Opsₘ : List Sortsₘ × Sortsₘ → Set where
  pushₘ  : (n : ℕ) → Opsₘ ([] ⇒ C)
  loadₘ  : (v : Var) → Opsₘ ([] ⇒ C)
  addₘ   : Opsₘ ([] ⇒ C)
  seqₘ   : Opsₘ ([ C , C ] ⇒ C)

Σₘ : Signature
Σₘ = ⟨ Sortsₘ , Opsₘ ⟩
\end{code}
 
The main aspect of the algebraic approach to correct translation is to
conceive both languages as algebras of the source signature. We could
define a $\Sigma_e$-algebra $\widetilde{\mathcal{T}_m}$ where the interpretation of
sort |E| is the set of terms of the term algebra $\mathcal{T}_m$ and the
interpretation of operations is defined in the following way:
%if False
\begin{code}
open TermAlgebra Σₘ renaming (|T| to |Tc|)
open Algebra
open Signature
open InitHomo
push : ℕ → HU C 
push n = term (pushₘ n) ⟨⟩
load : Var → HU C
load v = term (loadₘ v) ⟨⟩
seq : HU C → HU C → HU C
seq c₀ c₁ = term seqₘ (c₀  ▹ (c₁ ▹ ⟨⟩))
add : HU C
add = term addₘ ⟨⟩
private
\end{code}
%endif
\begin{code}
  ⟦_⟧ : Sortsₑ → Setoid _ _
  ⟦ E ⟧ = |Tc| ⟦ C ⟧ₛ

iₒ : ∀ {ar s} →  ops Σₑ (ar ⇒ s) → ∥ ⟦_⟧ ✳ ar ∥ →
                 ∥ ⟦ s ⟧ ∥
iₒ (val n) ⟨⟩ = push n
iₒ (var x) ⟨⟩ = load x
iₒ (plus) ⟨⟨ c₀ , c₁ ⟩⟩ = seq c₀ (seq c₁ add)
\end{code}

\noindent where |push|, |load| and |seq| are smart
constructors for the terms of |HU C|.

%if False
\begin{code}
iₚ : ∀ {ar} {s} → (f : ops Σₑ (ar ⇒ s)) →
         {vs vs' : ∥ ⟦_⟧ ✳ ar ∥ } →
         _∼v_ {R = λ s → Setoid._≈_ (⟦ s ⟧)} vs vs' →
         Setoid._≈_ (⟦  s ⟧) (iₒ f vs) (iₒ f vs')
iₚ (val n) {⟨⟩} ∼⟨⟩ = refl
iₚ plus {v₀ ▹ (v₀' ▹ ⟨⟩)} {v₁ ▹ (v₁' ▹ ⟨⟩)} (∼▹ v₀≈v₁ (∼▹ v₀'≈v₁' ∼⟨⟩)) =
                         cong₂ (λ c c' → seq c (seq c' add)) v₀≈v₁ v₀'≈v₁'
iₚ (var v) {⟨⟩} ∼⟨⟩ =  refl
\end{code}
%endif
\newcommand{\mapSort}[2]{#1\,#2}
\newcommand{\mapOp}[2]{#1\,#2}
\newcommand{\sdash}[1]{\vdash\!\!\!\!^{#1}}

Notice that turning $\mathcal{T}_m$ into a $\Sigma_e$-algebra is not
enough to transform any $\Sigma_m$-algebra, say $\mathcal{A}$, into a
$\Sigma_e$-algebra, because terms are not formal words that can be further
interpreted. To be precise, |c₀| and |c₁| in the third clause
of |iₒ| are meta-variables ranging over terms and not object variables
that could be later interpreted as projections.
%TODO: esta construcción se parece a otras en la literatura:
% buscar cuáles y citarlas, al menos decir que no es nada nuevo.
This can be solved by introducing a notion of \textit{formal terms},
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
%if False
\begin{code}
open import Data.Fin
module FormalTerm (Σ : Signature) where
\end{code}
%endif
\begin{code}
 data _⊢_  (ar' : Arity Σ) : (sorts Σ) → Set where
   var      : (n : Fin (length ar')) → ar' ⊢ (ar' ‼ n)
   op  : ∀ {ar s} → ops Σ (ar ⇒ s) → 
               HVec (ar' ⊢_) ar → ar' ⊢ s
\end{code}
A formal term $\mathit{ar} \sdash{\Sigma} t : s$ can be interpreted
in any $\Sigma$-algebra as a function from |⟦ ar ⟧ₛ*| to  |⟦ s ⟧ₛ|;
In fact, this function respects the equivalence relation of the setoid,
being |congᵒ| the name of that proof. 
%if False
\begin{code}
module FormalTermInt {ℓ₁ ℓ₂} {Σ : Signature} (A : Algebra {ℓ₁} {ℓ₂} Σ) where
 open FormalTerm Σ
 open Algebra
 mutual
\end{code}
%endif
\begin{code}
  ⟦_⟧ᵒ : ∀ {ar s} → ar ⊢ s → ∥ A ⟦ ar ⟧ₛ* ∥ → ∥ A ⟦ s ⟧ₛ ∥
  ⟦ var n ⟧ᵒ    as =  as ‼v n
  ⟦ op f ts ⟧ᵒ  as = A ⟦ f ⟧ₒ ⟨$⟩ ⟦ ts ⟧ᵒ* as
\end{code}
%if False
\begin{code}
  ⟦_⟧ᵒ* : ∀ {ar ar'} → HVec (ar ⊢_) ar' → ∥ A ⟦ ar ⟧ₛ* ∥ → ∥ A ⟦ ar' ⟧ₛ* ∥
  ⟦ ⟨⟩ ⟧ᵒ*      as = ⟨⟩
  ⟦ t ▹ ts ⟧ᵒ*  as = ⟦ t ⟧ᵒ as ▹ ⟦ ts ⟧ᵒ*  as

 mutual
  congᵒ : ∀ {ar s} {vs vs' : ∥ A ⟦ ar ⟧ₛ* ∥ } →
            (t : ar ⊢ s) →
            _∼v_  {R = Setoid._≈_ ∘ _⟦_⟧ₛ A} vs vs' →
            Setoid._≈_ (A ⟦ s ⟧ₛ) (⟦ t ⟧ᵒ vs) (⟦ t ⟧ᵒ vs')
  congᵒ {vs = vs} {vs'} (var n) eq = ~v-pointwise vs vs' eq n
  congᵒ {ar} {_} {vs} {vs'} (op f ts) eq = Π.cong (A ⟦ f ⟧ₒ) (congᵒ* ts)
    where  congᵒ* : ∀ {ar'} →
                   (ts : HVec (ar ⊢_) ar') →
                   (⟦ ts ⟧ᵒ* vs ) ∼v (⟦ ts ⟧ᵒ* vs' )
           congᵒ* ⟨⟩ = ∼⟨⟩
           congᵒ* (t ▹ ts) = ∼▹ (congᵒ t eq) (congᵒ* ts)
\end{code}
%endif

In order to define the transformation of algebras of the target signature
$\Sigma_t$ to algebras of the source signature $\Sigma_e$,
we need give a sort of $\Sigma_t$ for each
sort of $\Sigma_s$, and a formal term of $\Sigma_t$ for each operation
of $\Sigma_s$. A \emph{signature translation} consists of two functions,
mapping sorts and operations:


%% The translation of signatures is given by a pair of functions
%% $\mapSort{\_} : \mathit{sorts}\,Σ \to \mathit{sorts}\,Σ'$ and
%% $\mapOp{\_}$ mapping any operation
%% $f : [s_1,\ldots,s_{n}] \Rightarrow s$ to a $\Sigma'$-formal term:
%% $ \mapSort{s_1},\ldots, \mapSort{s_{n}} \sdash{\Sigma'} t: \mapSort{s}$.

%if False
\begin{code}
record _↝_ (Σₛ Σₜ : Signature) : Set where
 open FormalTerm Σₜ
 field
  ↝ₛ : sorts Σₛ → sorts Σₜ
  ↝ₒ : ∀ {ar s}  → ops Σₛ (ar , s) → lmap ↝ₛ ar ⊢ ↝ₛ s
\end{code}
%endif

\begin{spec}
record _↝_ (Σₛ Σₜ : Signature) : Set where
 field
  ↝ₛ : sorts Σₛ → sorts Σₜ
  ↝ₒ : ∀ {ar s} →  ops Σₛ (ar , s) →
                   map ↝ₛ ar ⊢ ↝ₛ s
\end{spec}
\newcommand{\intSign}[2]{#1 \hookrightarrow #2}
\newcommand{\algTrans}[1]{\widetilde{\mathcal{#1}}}

\paragraph{Transformation of Algebras} A signature translation
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
obtained by the interpretation of the corresponding formal expression:
$\algTrans{A} \llbracket f \rrbracket_o = \mathcal{A} \llbracket
\mapOp{t}{f}\, \rrbracket^o $.
We can formalize the transformation of algebra directly from this, however
the interpretation of operations is a little more complicated, since we need to convince Agda
that any vector |vs : VecH' (A ⟦_⟧ₛ ∘ ↝ₛ) is| has also the type
|VecH' A (map ↝ₛ is)|. This is accomplished with |reindex|.

\begin{code}
module AlgTrans {Σₛ Σₜ}  {t : Σₛ ↝ Σₜ} where
\end{code}
%if false
\begin{code}
 open _↝_
\end{code}
%endif
\begin{code}
 _⟨_⟩ₛ : ∀  {ℓ₀ ℓ₁} → (A : Algebra {ℓ₀} {ℓ₁} Σₜ) →
            (s : sorts Σₛ) → Setoid _ _
 A ⟨ s ⟩ₛ = A ⟦ ↝ₛ t s ⟧ₛ
\end{code}
\begin{code}
 _⟨_⟩ₒ :  ∀  {ℓ₀ ℓ₁ ar s} → (A : Algebra {ℓ₀} {ℓ₁} Σₜ) →
             ops Σₛ (ar ⇒ s) →
             (A ⟨_⟩ₛ) ✳ ar ⟶  A ⟨ s ⟩ₛ
 A ⟨ f ⟩ₒ = record  {  _⟨$⟩_ = ⟦ ↝ₒ t f ⟧ᵒ ∘ reindex (↝ₛ t) 
                       ;  cong =  congᵒ (↝ₒ t f) ∘
                                  ∼v-reindex (↝ₛ t) }
                                  
\end{code}
%if False
\begin{code}
    where open FormalTermInt A
\end{code}
%endif
\begin{code}
 〈_〉 : ∀ {ℓ₀ ℓ₁} → Algebra {ℓ₀} {ℓ₁} Σₜ → Algebra Σₛ
 〈 A 〉 = 〈 A ⟨_⟩ₛ , (A ⟨_⟩ₒ) 〉
\end{code}

Furthermore, we can also translate any homomorphism $h : \mathcal{A}
\to \mathcal{A'}$ to an homomorphism $\widetilde{h} :
\widetilde{\mathcal{A}} \to \widetilde{\mathcal{A'}}$, thus completing the
definition of a functor from the category of $\Sigma_t$-algebras to the
category of $\Sigma_s$-algebras. The proof |hcond↝| is the condition
of the transformed homomorphism, we omit it in this text.

%if False
\begin{code}
 open Hom
 open Homo
 open FormalTerm Σₜ
 hcond↝ : ∀ {l₀ l₁ l₂ l₃}
            {A : Algebra {l₀} {l₁} Σₜ}
            {A' : Algebra {l₂} {l₃} Σₜ}
            {ty : Type Σₛ} → (h : Homo A A') → 
            (f : ops Σₛ ty) → homCond 〈 A 〉 〈 A' 〉 ty (′ h ′ ∘ ↝ₛ t) f 
 hcond↝  {A = A} {A'} {ar ⇒ s} h f as = 
                   subst (λ vec → Setoid._≈_ (A' ⟦ ↝ₛ t s ⟧ₛ)
                                  (′ h ′ (↝ₛ t s) ⟨$⟩
                                         ⟦_⟧ᵒ A (↝ₒ t f) (reindex (↝ₛ t) as))
                                  (⟦_⟧ᵒ A' (↝ₒ t f) vec) 
                                   )
                     (mapReindex (↝ₛ t) 
                                 (_⟨$⟩_ ∘ ′ h ′)  as)
                     (homCond↝' (lmap (↝ₛ t) ar) (↝ₛ t s) (↝ₒ t f)
                                 (reindex (↝ₛ t) as))

  where open FormalTermInt
        homCond↝' : (ar' : Arity Σₜ) → (s' : sorts Σₜ) → (e : ar' ⊢ s') →
                    (vs : ∥ A ⟦ ar' ⟧ₛ* ∥ ) →                   
                    Setoid._≈_ (_⟦_⟧ₛ A' s')
                           (′ h ′ s' ⟨$⟩ ⟦_⟧ᵒ A e vs)
                           (⟦ A' ⟧ᵒ e (map⟿ A A' ′ h ′ vs))
        homCond↝' [] _ (var ()) ⟨⟩                           
        homCond↝' (s ∷ ar) .s (var zero) (v ▹ vs) = Setoid.refl (A' ⟦ s ⟧ₛ)
        homCond↝' (s ∷ ar) .(ar ‼ n) (var (suc n)) (v ▹ vs) = homCond↝' ar (ar ‼ n) (var n) vs
        homCond↝' ar s (op {ar₁} f₁ es) vs =
                   Setoid.trans (A' ⟦ s ⟧ₛ) (cond h f₁ (⟦_⟧ᵒ* A es vs))
                                            (Π.cong (A' ⟦ f₁ ⟧ₒ)
                                                    (homCond↝'vec ar₁ es))
          where homCond↝'vec : (ar₁ : Arity Σₜ) → 
                               (es : HVec (_⊢_ ar) ar₁) →
                               _∼v_ {R = Setoid._≈_ ∘ (A' ⟦_⟧ₛ) }
                               (map (λ x → _⟨$⟩_ (′ h ′ x)) (⟦_⟧ᵒ* A es vs))
                               (⟦_⟧ᵒ* A' es (map (λ x → _⟨$⟩_ (′ h ′ x)) vs))
                homCond↝'vec .[] ⟨⟩ = ∼⟨⟩
                homCond↝'vec (s₁ ∷ ar₁) (e ▹ es) = ∼▹ (homCond↝' ar s₁ e vs)
                                                       (homCond↝'vec ar₁ es)


module HomoTrans {Σₛ Σₜ}  {t : Σₛ ↝ Σₜ} {l₀ l₁ l₂ l₃} 
   {A : Algebra {l₀} {l₁} Σₜ}  
   {A' : Algebra {l₂} {l₃} Σₜ} where
   open AlgTrans {t = t}
   open _↝_
   open Hom
   open Homo
\end{code}
%endif
\begin{code}
   〈_〉ₕ : Homo A A' → Homo 〈 A 〉 〈 A' 〉
   〈 h 〉ₕ = record  { ′_′ = ′ h ′ ∘ ↝ₛ t
                    ; cond = hcond↝ h }
\end{code}

