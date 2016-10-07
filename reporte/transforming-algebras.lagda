%if False
\begin{code}
module reporte.transforming-algebras where
open import reporte.univ-alg
\end{code}
%endif
\section{Algebra transformation}
\label{sec:trans}

With our formalization thus far, the source language is given by the
term algebra of the signature $\Sigma_e$ and, parallely, the target 
language is the term algebra of the following signature:
\begin{code}
data Sortsₘ : Set where Code : Sortsₘ

data Opsₘ : List Sortsₘ × Sortsₘ → Set where
  pushₘ  : (n : ℕ) → Opsₘ ([] ⇒ Code)
  loadₘ  : (v : Var) → Opsₘ ([] ⇒ Code)
  addₘ   : Opsₘ ([] ⇒ Code)
  seqₘ   : Opsₘ ([ Code , Code ] ⇒ Code)

Σₘ : Signature
Σₘ = ⟨ Sortsₘ , Opsₘ ⟩
\end{code}
 
The main aspect of the algebraic approach to correct translation is to
conceive both languages as algebras of the source signature. We could
define a $\Sigma_e$-algebra $\widehat{\mathcal{T}_m}$ where the interpretation of
sort |ExprN| is the set of terms of the term algebra $\mathcal{T}_m$ and the
interpretation of operations is defined in the following way:
%if False
\begin{code}
open TermAlgebra Σₘ renaming (|T| to |Tc|)
open Algebra
open Signature
open InitHomo
push : ℕ → HU Code 
push n = term (pushₘ n) ⟨⟩
load : Var → HU Code
load v = term (loadₘ v) ⟨⟩
seq : HU Code → HU Code → HU Code
seq c₀ c₁ = term seqₘ (c₀  ▹ (c₁ ▹ ⟨⟩))
add : HU Code
add = term addₘ ⟨⟩
\end{code}
%endif
\begin{code}
⟦_⟧ : Sortsₑ → Setoid _ _
⟦ _ ⟧ = |Tc| ⟦ Code ⟧ₛ

iₒ : ∀ {ar s} → ops Σₑ (ar ⇒ s) → ∥ ⟦_⟧ ✳ ar ∥ → ∥ ⟦ s ⟧ ∥
iₒ (valN n) ⟨⟩ = push n
iₒ (varN x) ⟨⟩ = load x
iₒ (plus) ⟨⟨ c₀ , c₁ ⟩⟩ = seq c₀ (seq c₁ add)
\end{code}
%if False
\begin{code}
iₚ : ∀ {ar} {s} → (f : ops Σₑ (ar ⇒ s)) →
         {vs vs' : ∥ ⟦_⟧ ✳ ar ∥ } →
         _∼v_ {R = λ s → Setoid._≈_ (⟦ s ⟧)} vs vs' →
         Setoid._≈_ (⟦  s ⟧) (iₒ f vs) (iₒ f vs')
iₚ (valN n) {⟨⟩} ∼⟨⟩ = refl
iₚ plus {v₀ ▹ (v₀' ▹ ⟨⟩)} {v₁ ▹ (v₁' ▹ ⟨⟩)} (∼▹ v₀≈v₁ (∼▹ v₀'≈v₁' ∼⟨⟩)) =
                         cong₂ (λ c c' → seq c (seq c' add)) v₀≈v₁ v₀'≈v₁'
iₚ (varN v) {⟨⟩} ∼⟨⟩ =  refl
\end{code}
%endif
\newcommand{\mapSort}[1]{\widehat{#1}}
\newcommand{\mapOp}[1]{\widehat{#1}}
\newcommand{\sdash}[1]{\vdash\!\!\!\!^{#1}}

Notice that turning $\mathcal{T}_m$ into a $\Sigma_e$-algebra is not
enough to transform any $\Sigma_m$-algebra, say $\mathcal{A}$ into a
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
               Vec (ar' ⊢_) ar → ar' ⊢ s
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
  ⟦_⟧ᵒ* : ∀ {ar ar'} → Vec (ar ⊢_) ar' → ∥ A ⟦ ar ⟧ₛ* ∥ → ∥ A ⟦ ar' ⟧ₛ* ∥
  ⟦ ⟨⟩ ⟧ᵒ*      as = ⟨⟩
  ⟦ t ▹ ts ⟧ᵒ*  as = ⟦ t ⟧ᵒ as ▹ ⟦ ts ⟧ᵒ*  as

 mutual
  congᵒ : ∀ {ar s} {vs vs' : ∥ A ⟦ ar ⟧ₛ* ∥ } →
            (t : ar ⊢ s) →
            _∼v_  {R = Setoid._≈_ ∘ _⟦_⟧ₛ A} vs vs' →
            Setoid._≈_ (A ⟦ s ⟧ₛ) (⟦ t ⟧ᵒ vs) (⟦ t ⟧ᵒ vs')
  congᵒ {vs = vs} {vs'} (var n) eq = ~v‼prop vs vs' eq n
  congᵒ {ar} {_} {vs} {vs'} (op f ts) eq = Π.cong (A ⟦ f ⟧ₒ) (congᵒ* ts)
    where  congᵒ* : ∀ {ar'} →
                   (ts : Vec (ar ⊢_) ar') →
                   (⟦ ts ⟧ᵒ* vs ) ∼v (⟦ ts ⟧ᵒ* vs' )
           congᵒ* ⟨⟩ = ∼⟨⟩
           congᵒ* (t ▹ ts) = ∼▹ (congᵒ t eq) (congᵒ* ts)
\end{code}
%endif

We will use this denotation of formal terms to define the translation
of algebras; however the translation of signatures involves only
syntacticalities. In fact, it is given by a pair of functions
$\mapSort{\_} : \mathit{sorts}\,Σ \to \mathit{sorts}\,Σ'$ and
$\mapOp{\_}$ mapping any operation
$f : [s_1,\ldots,s_{n}] \Rightarrow s$ to a $\Sigma'$-formal term:
$ \mapSort{s_1},\ldots, \mapSort{s_{n}} \sdash{\Sigma'} t: \mapSort{s}$.

%if False
\begin{code}
record _↝_ (Σₛ Σₜ : Signature) : Set where
 open FormalTerm Σₜ
 field
  ↝ₛ : sorts Σₛ → sorts Σₜ
  ↝ₒ : ∀ {ar s} → ops Σₛ (ar , s) → map ↝ₛ ar ⊢ ↝ₛ s
\end{code}
%endif

\begin{spec}
record _↝_ (Σₛ Σₜ : Signature) : Set where
 field
  ↝ₛ : sorts Σₛ → sorts Σₜ
  ↝ₒ : ∀ {ar s} → ops Σₛ (ar , s) → map ↝ₛ ar ⊢ ↝ₛ s
\end{spec}
\newcommand{\intSign}[2]{#1 \leadsto #2}
\newcommand{\algTrans}[1]{\widetilde{\mathcal{#1}}}

\paragraph{Translation of Algebras} A signature interpretation
$\intSign{\Sigma_s}{\Sigma_t}$ induces a translation of
$\Sigma_t$-algebras as $\Sigma_s$-algebras; notice the contravariance
of the translation with respect to the interpretation. This is a
well-known concept in the theory of institutions and
\citet{sannella2012foundations} use the notion \textit{reduct algebra
with respect to a derived signature morphism} for a translated algebra
induced by a signature intepretation.

Given a signature interpretation $\intSign{\Sigma_s}{\Sigma_t}$ and a
$\Sigma_t$-algebra $\mathcal{A}$, we denote with $\algTrans{A}$ its
translation as a $\Sigma_s$-algebra. It is clear that every sort $s$
of $\Sigma_s$ can be interpreted via the interpretation of the sort:
$\algTrans{A} \llbracket s \rrbracket_s = \mathcal{A} \llbracket
\mapSort{s} \rrbracket_s $.  The denotation of an operation $f$ is
obtained by the interpretation of the corresponding formal expression:
$\algTrans{A} \llbracket f \rrbracket_o = \mathcal{A} \llbracket
\mapOp{f}\, \rrbracket^o $. In Agda the first component of the
translated algebra mimics that definition, however we need to convince
Agda that any vector |vs : VecH' (A ⟦_⟧ₛ ∘ ↝ₛ) is| has also the type
|VecH' A (map ↝ₛ is)|, this is accomplished with |reindex|.

%if False
\begin{code}
module AlgTrans {Σₛ Σₜ}  {i : Σₛ ↝ Σₜ} where
 open _↝_
\end{code}
%endif
\begin{code}
 _⟨_⟩ₒ :  ∀ {l₀ l₁ ar s} →
       (A : Algebra {l₀} {l₁} Σₜ) → ops Σₛ (ar ⇒ s) →
       (A ⟦_⟧ₛ ∘ (↝ₛ i)) ✳ ar ⟶ A ⟦ ↝ₛ i s ⟧ₛ
 A ⟨ f ⟩ₒ = record {  
               _⟨$⟩_ = ⟦ ↝ₒ i f ⟧ᵒ ∘ reindex (↝ₛ i) 
             ;  cong = congᵒ (↝ₒ i f) ∘ ∼v-reindex (↝ₛ i) }
\end{code}
%if False
\begin{code}
    where open FormalTermInt A
\end{code}
%endif
\begin{code}
 〈_〉 : ∀ {l₀ l₁} → Algebra {l₀} {l₁} Σₜ → Algebra Σₛ
 〈 A 〉 = 〈 (A ⟦_⟧ₛ ∘ ↝ₛ i) , (A ⟨_⟩ₒ) 〉
\end{code}

Furthermore, we can also translate any homomorphism $h : \mathcal{A}
\to \mathcal{A'}$ to an homomorphism $\widehat{h} :
\widehat{\mathcal{A}} \to \widehat{\mathcal{A'}}$, thus completing the
definition of a functor from the category of $\Sigma_t$-algebras to the
category of $\Sigma_s$-algebras.

%if False
\begin{code}
 open Hom
 open Homo
 open FormalTerm Σₜ
 hcond↝ : ∀ {l₀ l₁ l₂ l₃}
            {A : Algebra {l₀} {l₁} Σₜ}
            {A' : Algebra {l₂} {l₃} Σₜ}
            {ty : Type Σₛ} → (h : Homo A A') → 
            (f : ops Σₛ ty) → homCond 〈 A 〉 〈 A' 〉 ty (′ h ′ ∘ ↝ₛ i) f 
 hcond↝  {A = A} {A'} {ar ⇒ s} h f as = 
                   subst (λ vec → Setoid._≈_ (A' ⟦ ↝ₛ i s ⟧ₛ)
                                  (′ h ′ (↝ₛ i s) ⟨$⟩
                                         ⟦_⟧ᵒ A (↝ₒ i f) (reindex (↝ₛ i) as))
                                  (⟦_⟧ᵒ A' (↝ₒ i f) vec) 
                                   )
                     (≡maptransf (↝ₛ i) (Setoid.Carrier ∘ _⟦_⟧ₛ A)
                                        (Setoid.Carrier ∘ _⟦_⟧ₛ A')
                                 (_⟨$⟩_ ∘ ′ h ′) ar as)
                     (homCond↝' (map (↝ₛ i) ar) (↝ₛ i s) (↝ₒ i f)
                                 (reindex (↝ₛ i) as))

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
                               (es : Vec (_⊢_ ar) ar₁) →
                               _∼v_ {R = Setoid._≈_ ∘ (A' ⟦_⟧ₛ) }
                               (mapV (λ x → _⟨$⟩_ (′ h ′ x)) (⟦_⟧ᵒ* A es vs))
                               (⟦_⟧ᵒ* A' es (mapV (λ x → _⟨$⟩_ (′ h ′ x)) vs))
                homCond↝'vec .[] ⟨⟩ = ∼⟨⟩
                homCond↝'vec (s₁ ∷ ar₁) (e ▹ es) = ∼▹ (homCond↝' ar s₁ e vs)
                                                       (homCond↝'vec ar₁ es)


module HomoTrans {Σₛ Σₜ}  {i : Σₛ ↝ Σₜ} {l₀ l₁ l₂ l₃} 
   {A : Algebra {l₀} {l₁} Σₜ}  
   {A' : Algebra {l₂} {l₃} Σₜ} where
   open AlgTrans {i = i}
   open _↝_
   open Hom
   open Homo
\end{code}
%endif
\begin{code}
   〈_〉ₕ : Homo A A' → Homo 〈 A 〉 〈 A' 〉
   〈 h 〉ₕ = record { ′_′ = ′ h ′ ∘ ↝ₛ i ; cond = hcond↝ h }
\end{code}

