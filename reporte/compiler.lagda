%if False
\begin{code}
module compiler where
open import univ-alg
open import transforming-algebras
\end{code}
%endif
\section{Back to McCarthy}
\label{sec:compiler}

McCarthy's reading of the correctness of the compiler is
\begin{quote}
the result of running the compiled program is to put the
value of the expression compiled into the accumulator.
\end{quote}
We expressed this condition as the equation 
\[
  \execCode\,(\comp\,e)\,(s,\sigma)\,=\,\evalExpr\,e\,\sigma \consop s \enspace .
\]
In this short section we show how the transformation of algebras
enables us to obtain that proof by initiality. In particular, we
define in Agda the algebra $\mathit{Exec}$,
corresponding to the execution of the target language, and also the
expected translation from the signature $\Sigma_e$ to the signature
$\Sigma_m$. This will let us obtain the compiler as the initial
homomorphism from $\mathcal{T}_e$ to $\widetilde{\mathcal{T}_m}$; thus
getting the following diagram between $\Sigma_e$-algebras:
\begin{center}
  \begin{tikzpicture}[>=latex]
    \node (te) at (0,1.5) {$T_e$}; 
    \node (tc) at (3,1.5) {$\widetilde{T_m}$}; 
    \node (seme) at (0,0) {$\mathit{Sem}$} ; 
    \node (semc) at (3,0) {$\widetilde{\mathit{Exec}}$} ; 
    \path [->,shorten <=2pt,shorten >=2pt] (te) edge node [above] {$\mathit{comp}$} (tc); 
    \path [->,shorten <=2pt,shorten >=2pt] (te) edge node [left] {$\mathit{hsem}$} (seme); 
    \path [->,shorten <=2pt,shorten >=2pt] (tc) edge node [right] {$\widetilde{\mathit{hexec}}$} (semc);
  \end{tikzpicture}
\end{center}
To close the gap, we define an homomorphism
$\mathit{enc} : \mathit{Sem} \to \widetilde{\mathit{Exec}}$; in order
to show that this approach corresponds to the usual notion of compiler
correctness, we extract a proof from the commuting diagram.



\paragraph{Semantics of the target language}

As we explained in the introduction, our target language corresponds
to a stack-based machine. Execution can get stuck when the current
instruction is $\instr{add}$ and there is less than two naturals in
the stack. We model partiality with the Maybe monad.
%if False
\begin{code}
Stack : Set
Stack = List ℕ

Conf : Set
Conf = Stack × State
open import Data.Maybe hiding (map)
open import Category.Monad
open import Category.Monad.Identity 
open Signature
private
\end{code}
%endif
\begin{code}
  ⟦_⟧ₛᵐ : sorts Σₘ → Setoid _ _
  ⟦ Codeₛ ⟧ₛᵐ = Conf →-setoid Maybe Stack
\end{code}

The interpretation of the operations is straightforward: the machine
gets stuck only when incurring in a stack underflow; in such case,
errors are propagated and the following instructions are discarded.
\begin{code}
iₒᵐ : ∀ {ar s} →  ops Σₘ (ar ⇒ s) →
                  ∥ ⟦_⟧ₛᵐ ✳ ar ∥ → ∥ ⟦ s ⟧ₛᵐ ∥
iₒᵐ (pushₘ n) ⟨⟩ (s , σ) = just (n ∷ s)
iₒᵐ (loadₘ v) ⟨⟩ (s , σ) = just (σ v ∷ s)
iₒᵐ addₘ ⟨⟩ (m ∷ n ∷ s , σ) = just (m + n ∷ s)
iₒᵐ addₘ ⟨⟩ (s , σ) = nothing
iₒᵐ seqₘ ⟨⟨ v₀ , v₁ ⟩⟩ (s , σ) =  v₀ (s , σ) >>=
                                  (λ s' → v₁ (s' , σ))
\end{code}
%if False
\begin{code}
  where open RawMonad Data.Maybe.monad
iₚᵐ : ∀ {ar} {s} → (f : ops Σₘ (ar ⇒ s)) →
           {vs vs' : ∥ ⟦_⟧ₛᵐ ✳ ar ∥ } →
           _∼v_ {R = Setoid._≈_ ∘ ⟦_⟧ₛᵐ} vs vs' →
           Setoid._≈_ (⟦ s ⟧ₛᵐ) (iₒᵐ f vs) (iₒᵐ f vs')
iₚᵐ (pushₘ n) ∼⟨⟩ = Setoid.refl ⟦ C ⟧ₛᵐ
iₚᵐ (loadₘ v) ∼⟨⟩ = Setoid.refl ⟦ C ⟧ₛᵐ
iₚᵐ addₘ ∼⟨⟩ = Setoid.refl ⟦ C ⟧ₛᵐ
iₚᵐ seqₘ {⟨⟨ t₁ , t₃ ⟩⟩} {⟨⟨ t₂ , t₄ ⟩⟩}
         (∼▹ t₁≈t₂ (∼▹ t₃≈t₄ ∼⟨⟩)) (s , σ) = begin
                                             ((t₁ (s , σ)) >>= (λ s' → t₃ (s' , σ)))
                                             ≡⟨ cong (_>>= λ s' → t₃ (s' , σ)) (t₁≈t₂ (s , σ)) ⟩
                                             ((t₂ (s , σ)) >>= (λ s' → t₃ (s' , σ)))
                                             ≡⟨ congSeq ⟩
                                             ((t₂ (s , σ)) >>= (λ s' → t₄ (s' , σ)))
                                             ∎
    where open RawMonad Data.Maybe.monad
          import Relation.Binary.PropositionalEquality
          open ≡-Reasoning
          congSeq : (t₂ (s , σ) >>= (λ s' → t₃ (s' , σ)))
                    ≡
                    (t₂ (s , σ) >>= (λ s' → t₄ (s' , σ)))
          congSeq with t₂ (s , σ)
          ... | nothing = refl
          ... | just s' = t₃≈t₄ (s' , σ)        
\end{code}
%endif

The interpretation of operations is completed by the proof that the
function |iₒᵐ| respects the equality of arguments; we
omit this straightforward proof, which we call |iₚᵐ|. 
\begin{code}
iₘ :  ∀ {ar s} →  ops Σₘ (ar ➜ s) →
                  ⟦_⟧ₛᵐ ✳ ar ⟶ ⟦ s ⟧ₛᵐ
iₘ f = record { _⟨$⟩_ = iₒᵐ f ; cong = iₚᵐ f }
\end{code}
We have thus constructed the algebra |Exec|; the semantics of low-level
programs, represented as elements in | |T|ₘ |, is given by the initial
homomorphism.
%if False
\begin{code}
open TermAlgebra Σₑ renaming (|T| to |Tₑ|)
open TermAlgebra Σₘ renaming (|T| to |Tₘ|)
open Hom
open InitHomo
\end{code}
%endif
\begin{code}
Exec : Algebra Σₘ
Exec = 〈 ⟦_⟧ₛᵐ , iₘ 〉

semₘ : Homo |Tₘ| Exec
semₘ = |h| Exec
\end{code}
%if False
\begin{code}
open FormalTerm Σₘ
open import Data.Fin
\end{code}
%endif

\paragraph{Translating the source language}
Our next task is to define a translation from |Σₑ| to |Σₘ|. Remember that this involves
a translation of sorts
\begin{code}
s↝ : sorts Σₑ → sorts Σₘ
s↝ E = C
\end{code}
and a translation of operations, which consists in assigning a
formal expression $\mathit{ar} \vdash t : s$ to each operation symbol
$f : ar \Rightarrow s$. 
\begin{spec}
op↝ : ∀ {ar s} → ops Σₑ (ar , s) → map s↝ ar ⊢ s↝ s
op↝ (val n) = op (pushₘ n) ⟨⟩
op↝ (var v) = op (loadₘ v) ⟨⟩
op↝ plus = op seqₘ  ⟨⟨  var (suc zero)
                    ,  op seqₘ ⟨⟨ var zero , op addₘ ⟨⟩ ⟩⟩
                     ⟩⟩
\end{spec}

%if false
\begin{code}
op↝ : ∀ {ar s} → ops Σₑ (ar , s) → lmap s↝ ar ⊢ s↝ s
op↝ (val n) = op (pushₘ n) ⟨⟩
op↝ (var v) = op (loadₘ v) ⟨⟩
op↝ plus = op seqₘ  ⟨⟨  var (suc zero)
                    ,  op seqₘ ⟨⟨ var zero , op addₘ ⟨⟩ ⟩⟩
                     ⟩⟩
\end{code}
%endif

Note that the translation of operations corresponds with the
informal definition of the compiler that we described in the
introduction.

The following translation will induce the transformation of
$\Sigma_m$-algebras into $\Sigma_e$-algebras.
\begin{code}
e↝m : Σₑ ↝ Σₘ
e↝m = record  { ↝ₛ = s↝ ; ↝ₒ = op↝ }
\end{code}
In particular we can see the term algebra |Tₘ| as a $\Sigma_e$-algebra:

\begin{code}
open AlgTrans {t = e↝m}
\end{code}

\begin{code}
Codeₑ : Algebra Σₑ
Codeₑ = 〈 |Tₘ| 〉
\end{code}
and the initial homomorphism from |Tₑ| to |〈 Tₘ 〉| is the compiler.
\begin{code}
hcomp : Homo |Tₑ| Codeₑ
hcomp = |h| Codeₑ
\end{code}

Moreover the low-level semantics of a high-level program is obtained by
composing |hcomp| with $\widehat{\mathit{exec}} : \mathcal{T}_m \to \mathit{Exec}$.
\begin{code}
Execₑ : Algebra Σₑ
Execₑ = 〈 Exec 〉

execₑ : Homo |Tₑ| Execₑ
execₑ = 〈 semₘ 〉ₕ ∘ₕ hcomp
\end{code}
%if False
\begin{code}
 where open HomoTrans {t = e↝m} {A = |Tₘ|} {A' = Exec}
       open HomComp {A₀ = |Tₑ|} {Codeₑ} {Execₑ}
\end{code}
%endif
Of course, this semantics is also given by the initial homomorphism from
|Tₑ| to |Codeₑ| and both are extensionally equal.
\begin{code}
execₑ' : Homo |Tₑ| Execₑ
execₑ' = |h| Execₑ
\end{code}


To complete the diagram we need a homomorphism from
$\mathit{Sem} = \mathit{State} \to \mathbb{N}$ to
$\widetilde{\mathit{Exec}} = \mathit{Stack}\times \mathit{State} →
\mathit{Maybe}\ \mathit{Stack}$.

\noindent Remember that besides the function
$\mathit{enc} : \mathit{Sem} → \mathit{Exec}$ we have to provide a
proof of the homomorphism condition, Agda's type-checker tells us,
for example, that $\mathit{enc}$ should satisfy:
\begin{spec}
  enc (′ hsem ′ (val n) ⟨⟩) (s , σ) = just (n ∷ s)
\end{spec}
Since |′ hsem ′ (val n) ⟨⟩ σ = n| we can generalize this
situation and define
\begin{code}
enc : Semₑ ⟿ Execₑ
enc E = record  {
    _⟨$⟩_ = λ {f (s , σ) → just (f σ ∷ s) }
  ; cong =  λ { f≈g (s , σ) → cong  (λ n → just (n ∷ s))
                                    (f≈g σ) }
  }
\end{code}

Now Agda infers that the proof obligation for |enc| satisfying the
homomorphism condition amounts to prove the equality of the same Agda
terms.
\begin{code}
condEnc : ∀ {ty}  (f : ops Σₑ ty) →
                  homCond Semₑ Execₑ ty enc f
condEnc (val n)   ⟨⟩           (s , σ) = refl
condEnc (var v)   ⟨⟩           (s , σ) = refl
condEnc plus       ⟨⟨ f , g ⟩⟩  (s , σ) = refl

encH : Homo Semₑ Execₑ
encH = record { ′_′ = enc ; cond = condEnc }
\end{code}

We have completed the diagram and get the correctness of the compiler.
\begin{center}
  \begin{tikzpicture}[>=latex]
    \node (te) at (0,1.5) {$T_e$}; 
    \node (tc) at (3,1.5) {$\widetilde{T_m}$}; 
    \node (seme) at (0,0) {$\mathit{Sem}$} ; 
    \node (semc) at (3,0) {$\widetilde{\mathit{Exec}}$} ; 
    \path [->,shorten <=2pt,shorten >=2pt] (te) edge node [above] {$\mathit{hcomp}$} (tc); 
    \path [->,shorten <=2pt,shorten >=2pt] (te) edge node [left] {$\mathit{hsem}$} (seme); 
    \path [->,shorten <=2pt,shorten >=2pt] (tc) edge node [right] {$\widetilde{\mathit{hexec}}$} (semc);
    \path [->,shorten <=2pt,shorten >=2pt] (seme.10) edge node [above] {$\mathit{enc}$} (semc.170);
  \end{tikzpicture}
\end{center}


The proof of correctness, as stated by McCarthy and Painter, is a consequence of
the initiality of | |Tₑ| |. We define types to have a short notation in the
proof of correctness.

%if false
\begin{code}
open Algebra
open Homo
open HomoTrans {t = e↝m} {A = |Tₘ|} {A' = Exec}
open HomComp
\end{code}
%endif

\begin{code}
Expr : _
Expr = ∥ |Tₑ| ⟦ E ⟧ₛ ∥

⟦_⟧_ : Expr → State → ℕ
⟦ e ⟧ σ = (′ |h| Semₑ ′ E ⟨$⟩ e) σ


⟪_⟫ : ∥ |Tₘ| ⟦ C ⟧ₛ ∥ → Conf → Maybe Stack
⟪ c ⟫ = ′ semₘ ′ C ⟨$⟩ c

compₑ : Expr → ∥ |Tₘ| ⟦ C ⟧ₛ ∥
compₑ e = ′ hcomp ′ E ⟨$⟩ e 
\end{code}

\begin{code}
correct : ∀  e s σ →
             ⟪ compₑ  e ⟫ (s , σ) ≡ just ((⟦ e ⟧ σ ) ∷ s) 
correct e s σ = proj₂  (isInitial Execₑ)
                       (〈 semₘ 〉ₕ ∘ₕ hcomp)
                       (encH ∘ₕ (|h| Semₑ))
                       E
                       e
                       (s , σ)
\end{code}
