%if False
\begin{code}
module reporte.compiler where
open import reporte.univ-alg
open import reporte.transforming-algebras
\end{code}
%endif
\section{Back to McCarthy}
\label{sec:compiler}

In this short section we define the expected interpretation of the
signature $\Sigma_e$, introduced in Sec.~\ref{sec:univ-alg}, in the
signature $\Sigma_c$, shown in Sec.~\ref{sec:trans}; this will let us
obtain the compiler as the initial homomorphism from $\mathcal{T}_e$
to $\widetilde{\mathcal{T}_m}$. We will also define the algebra
$\mathit{Exec}$ corresponding to the execution of the target language
thus getting the following diagram between $\Sigma_e$-algebras:
\begin{center}
  \begin{tikzpicture}[>=latex]
    \node (te) at (0,1.5) {$T_e$}; 
    \node (tc) at (3,1.5) {$\widetilde{T_c}$}; 
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

%TODO: ver cómo recordar esto por acá.
El objetivo es definir un compilador $comp\,:\,Expr \rightarrow Code$
tal que la ejecución del resultado de compilar una expresión $e$ a
partir de una pila $s$ y un estado $\sigma$ obtenga la misma pila $s$
con el valor semántico de $e$ agregado en el tope:
\[
  \execCode\,(\comp\,e)\,(\sigma,s)\,=\,\evalExpr\,e\,\sigma \consop s
\]


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
iₒᵐ : ∀ {ar s} → ops Σₘ (ar ⇒ s) → ∥ ⟦_⟧ₛᵐ ✳ ar ∥ → ∥ ⟦ s ⟧ₛᵐ ∥
iₒᵐ (pushₘ n) ⟨⟩ (s , σ) = just (n ∷ s)
iₒᵐ (loadₘ v) ⟨⟩ (s , σ) = just (σ v ∷ s)
iₒᵐ addₘ ⟨⟩ (m ∷ n ∷ s , σ) = just (m + n ∷ s)
iₒᵐ addₘ ⟨⟩ (s , σ) = nothing
iₒᵐ seqₘ ⟨⟨ v₀ , v₁ ⟩⟩ (s , σ) = v₀ (s , σ) >>= (λ s' → v₁ (s' , σ))
\end{code}
%if False
\begin{code}
  where open RawMonad Data.Maybe.monad
iₚᵐ : ∀ {ar} {s} → (f : ops Σₘ (ar ⇒ s)) →
           {vs vs' : ∥ ⟦_⟧ₛᵐ ✳ ar ∥ } →
           _∼v_ {R = Setoid._≈_ ∘ ⟦_⟧ₛᵐ} vs vs' →
           Setoid._≈_ (⟦ s ⟧ₛᵐ) (iₒᵐ f vs) (iₒᵐ f vs')
iₚᵐ (pushₘ n) ∼⟨⟩ = Setoid.refl ⟦ Code ⟧ₛᵐ
iₚᵐ (loadₘ v) ∼⟨⟩ = Setoid.refl ⟦ Code ⟧ₛᵐ
iₚᵐ addₘ ∼⟨⟩ = Setoid.refl ⟦ Code ⟧ₛᵐ
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

The interpretation of operations is completed by the proof that their
interpretation, here |iₒᵐ|, respects the equality of arguments; we
omit this straightforward proof, which we call |iₚᵐ|. 
\begin{code}
iₘ :  ∀ {ar s} → ops Σₘ (ar ➜ s) → ⟦_⟧ₛᵐ ✳ ar ⟶ ⟦ s ⟧ₛᵐ
iₘ f = record { _⟨$⟩_ = iₒᵐ f ; cong = iₚᵐ f }
\end{code}
We have thus constructed the algebra |Exec|; the semantics of low-level
programs, represented as elements in | |T|ₘ |, is given by the initial
homomorphism.
%if False
\begin{code}
open TermAlgebra Σₘ renaming (|T| to |Tₘ|)
open Hom
\end{code}
%endif
\begin{code}
Exec : Algebra Σₘ
Exec = 〈 ⟦_⟧ₛᵐ , iₘ 〉

semₘ : Homo |Tₘ| Exec
semₘ = hₘ
\end{code}
%if False
\begin{code}
  where open InitHomo Exec renaming (|h|A to hₘ)
open FormalTerm Σₘ
open import Data.Fin
\end{code}
%endif

\paragraph{Interpreting the source language}
Our next task is to interpret |Σₑ| into |Σₘ|. Remember that this involves
an interpretation of sorts
\begin{code}
s↝ : sorts Σₑ → sorts Σₘ
s↝ ExprN = Code
\end{code}
and an interpretation of operations, which consists in assigning a
formal expression $\mathit{ar} \vdash t : s$ to each operation symbol
$f : ar \Rightarrow s$. 
\begin{code}
op↝ : ∀ {ar s} → ops Σₑ (ar , s) → map s↝ ar ⊢ s↝ s
op↝ (valN n) = op (pushₘ n) ⟨⟩
op↝ (varN v) = op (loadₘ v) ⟨⟩
op↝ plus = op seqₘ
    ⟨⟨ var zero , op seqₘ ⟨⟨ var (suc zero) , op addₘ ⟨⟩ ⟩⟩ ⟩⟩
\end{code}

Podemos definir entonces la traducción de símbolos de función, y luego
la traducción de signaturas:

\begin{spec}
tfuncs : ∀ {ar} {s} →  (f : funcs Σₑ (ar , s)) →
                       ΣExpr Σₘ (map tsorts ar) (tsorts s)
tfuncs (valN n)  = valN↝ n
tfuncs plus      = plus↝
tfuncs (varN v)  = varN↝ v
\end{spec}

\begin{spec}
t : Σₑ ↝ Σₘ
t = record  { ↝ₛ = tsorts
            ; ↝f = tfuncs
            }
\end{spec}

\subsubsection*{Transformación de las álgebras de |Σₘ|}

Teniendo definida la traducción |t| podemos llevar las álgebras de |Σₘ| a
álgebras de |Σₑ| y preservar los homomorfismos:

\begin{spec}
  Codeₑ : Algebra Σₑ
  Codeₑ = t 〈 ∣T∣ Σₘ 〉
\end{spec}

\begin{spec}
  Execₑ : Algebra Σₑ
  Execₑ = t 〈 Exec 〉
\end{spec}

\begin{spec}
  hexecₑ : Homomorphism Codeₑ Execₑ
  hexecₑ = t 〈 ∣T∣ₕ Exec 〉ₕ
\end{spec}

Y por inicialidad del álgebra de términos de |Σₑ| tenemos un homomorfismo
entre ésta y el álgebra |Codeₑ|:

\begin{spec}
  hcomp : Homomorphism (∣T∣ Σₑ) Codeₑ
  hcomp = ∣T∣ₕ Codeₑ
\end{spec}

Ahora el diagrama se ve así:

%\begin{diagram}
%  |∣T∣ Σₑ|     &\rTo^{|homc|}  &|Codeₑ|\\
%  \dTo_{|∣T∣ₕ Semₑ|} &             &\dTo_{|hexecₑ|}\\
%  |Semₑ|        &              &|Execₑ|\\
%\end{diagram}

Para completar el diagrama y tener la prueba de corrección del compilador
tenemos que dar un homomorfismo entre |Semₑ| y |Execₑ|.

\subsubsection*{Homomorfismo entre semánticas}

Habíamos visto que la corrección del compilador está dada por la validez de la siguiente
igualdad:

\begin{center}
   $exec\,(comp\,e)\,(s,\upsigma)\,=\,eval\,e\,\upsigma\,:\,s$
\end{center}

Podemos ver una relación entre las semánticas de los dos lenguajes. Si $f$ es
una función en $State \rightarrow \mathbb{N}$ correspondiente a la
semántica de alguna expresión en $Expr$, la función semántica correspondiente
en $Code$ será la siguiente:

\begin{center}
   $\lambda\,(s , \upsigma)\,.\,f\,\upsigma:s$
\end{center}

Con esta idea podemos definir un homomorfismo entre |Semₑ| y |Execₑ|. Para ello
debemos dar una función los setoides correspondientes a la interpretación
de |E| en |Semₑ| y la de |E| en |Execₑ|, es decir
|(State → ℕ) ⟶ (Conf → Maybe Stack)|; y luego la prueba de condición de homomorfismo
la cual resultará trivial:

\begin{spec}
Enc : Semₑ ⟿ Execₑ
Enc E = record  { _⟨$⟩_ = λ {fₑ (s , σ) → just (fₑ σ ∷ s)}
                ; cong = ...
                }
\end{spec}

\begin{spec}
condhEnc : ∀ {ty}  (f : funcs Σₑ ty) →
                   homCond Semₑ Execₑ Enc f
condhEnc (valN n) ⟨⟩          = λ _ → refl
condhEnc plus (f₀ ▹ f₁ ▹ ⟨⟩)  = λ _ → refl
condhEnc (varN v) ⟨⟩          = λ _ → refl
\end{spec}

\begin{spec}
hEnc : Homomorphism Semₑ Execₑ
hEnc = record  { ′_′ = Enc
               ; cond = condhEnc
               }
\end{spec}

Con este homomorfismo tenemos que el siguiente diagrama conmuta:

%\begin{diagram}
%  |∣T∣ Σₑ|     &\rTo^{|homc|}  &|Codeₑ|\\
%  \dTo_{|∣T∣ₕ Semₑ|} &             &\dTo_{|hexecₑ|}\\
%  |Semₑ|        &\rTo^{|hEnc|}  &|Execₑ|\\
%\end{diagram}

\noindent es decir, |hexecₑ ∘ homc = hEnc ∘ ∣T∣ₕ Semₑ|.

\subsubsection*{Extracción de la prueba de corrección}

Podemos extraer a partir del desarrollo realizado con el framework
algebraico, la prueba de corrección del compilador correcto, de la manera
usual en que uno la realizaría.

\begin{spec}
Expr : Set
Expr = Carrier (∣T∣ Σₑ ⟦ E ⟧ₛ)
\end{spec}

\begin{spec}
⟦_⟧_ : Expr → State → ℕ
⟦ e ⟧ σ = (′ ∣T∣ₕ Semₑ ′ E ⟨$⟩ e) σ
\end{spec}

\begin{spec}
Code : Set
Code = Carrier (Codeₑ ⟦ E ⟧ₛ)
\end{spec}

\begin{spec}
⟪_⟫ : Code → Conf → Maybe Stack
⟪ c ⟫ = ′ hexecₑ ′ E ⟨$⟩ c
\end{spec}


\begin{spec}
compₑ : Expr → Code
compₑ e = ′ homc ′ E ⟨$⟩ e 
\end{spec}


\begin{spec}
correct : ∀  (e : Expr) → (s : Stack) → (σ : State) → 
             ⟪ compₑ e ⟫ (s , σ) ≡ just ((⟦ e ⟧ σ) ∷ s)
correct e s σ = (elim≈ₕ unic E e e refl) (s , σ)
  where  unic : (hexecₑ ∘ₕ homc) ≈ₕ (hₛₑₘ ∘ₕ homSem)
         unic = unique (∣T∣init Σₑ) Execₑ  (hexecₑ ∘ₕ homc)
                                           (hₛₑₘ ∘ₕ homSem)
\end{spec}


%% if : ∀ {ar} {s} →  (f : funcs Σₑ (ar , s)) →
%%                    VecH Sortsₑ (Carrier ∘ iSortsₑ) ar →
%%                    Carrier (iSortsₑ s)
%% if (valN n) ⟨⟩           = λ σ → n
%% if plus (v₀ ▹ v₁ ▹ ⟨⟩) σ = v₀ σ + v₁ σ
%% if (varN x) ⟨⟩           = λ σ → σ x

%% iFuncsₑ : ∀ {ty} → (f : funcs Σₑ ty) → IFuncs Σₑ ty iSortsₑ
%% iFuncsₑ f = record  { _⟨$⟩_ = if f
%%                     ; cong = ... }

%% Semₑ : Algebra Σₑ
%% Semₑ = iSortsₑ ∥ iFuncsₑ

%% hSem : Homomorphism ExprAlg Semₑ
%% hSem = ∣T∣ₕ Semₑ
%% \end{spec}





%% En esta sección mostraremos la corrección de un compilador de un lenguaje
%% de expresiones naturales sencillo, a un lenguaje de máquina, que manipula un
%% stack.

%% El lenguaje fuente tiene la siguiente sintaxis:

%% \begin{quote}
%% $ e  ::=  \;\; n  \;\; || \;\;  v \;\; || \;\; e_1 ⊕ e_2 $
%% \end{quote}

%% \noindent donde $n$ es una constante natural y $v$ una variable.

%% La semántica de este lenguaje es la esperada, obteniendo un valor natural a partir
%% de un estado de asignación de valores a las variables.

%% \medskip

%% El lenguaje target tiene la siguiente sintaxis:

%% \begin{quote}
%% $ c  ::=  \;\; push\,n  \;\; || \;\; load\, v \;\; || \;\; c_1 ; c_2 \;\; || \;\; add $
%% \end{quote}

%% \noindent donde $n$ es una constante natural y $v$ una variable.

%% Informalmente, la ejecución de un código del lenguaje target modificará una pila de elementos
%% naturales utilizando también un estado de asignación de valores a las variables.
%% $push\,n$ pone en el tope de la pila el valor $n$; $load\,v$ pone en el tope de la pila el valor
%% de la variable $v$ en el estado; $c_1 ; c_2$ ejecuta $c_1$ y luego $c_2$ a partir del stack resultante;
%% y por último $add$ a partir de una pila que tiene al menos dos elementos en el tope, los quita de la pila
%% y pone el resultado de sumarlos.

%% El compilador lo definiríamos de esta forma:

%% \begin{align*}
%%   comp\;n  &= push\;n\\
%%   comp\;v  &= load\;v\\
%%   comp\;e_1 \oplus e_2 &= comp\;e_1 ; comp\;e_2 ; add
%% \end{align*}


%% Procedamos a definir este compilador de manera correcta utilizando el framework presentado
%% en las secciones anteriores.

%% \subsection{Sintaxis}

%% Podemos definir la sintaxis de ambos lenguajes a partir de dos signaturas |Σₑ| y |Σₘ|,
%% obteniendo las respectivas álgebras de términos:

%% \subsubsection*{Sintaxis del lenguaje source}

%% \begin{spec}
%% data Sortsₑ : Sorts where
%%   ExprN : Sortsₑ

%% data Funcsₑ : Funcs Sortsₑ where
%%   valN  : (n : ℕ) → Funcsₑ ([] , ExprN)
%%   plus  : Funcsₑ ( ExprN ∷ [ ExprN ] , ExprN )
%%   varN  : (v : Var) → Funcsₑ ([] , ExprN)


%% Σₑ : Signature
%% Σₑ = record  { sorts = Sortsₑ
%%              ; funcs = Funcsₑ
%%              }

%% ExprAlg : Algebra Σₑ
%% ExprAlg = ∣T∣ Σₑ

%% \end{spec}

%% \noindent La expresión $3 \oplus ``x''$ del lenguaje source se corresponde con

%% \begin{spec}
%% term plus (term (valN 3) ⟨⟩ ▹ term (varN `` x '') ⟨⟩ ▹ ⟨⟩)
%% \end{spec}

%% \noindent en el álgebra de términos |ExprAlg|.

%% \subsubsection*{Sintaxis del lenguaje target}

%% \begin{spec}
%% data Sortsₘ : Sorts where
%%   Codeₛ : Sortsₘ

%% data Funcsₘ : Funcs Sortsₘ where
%%   pushₘ  : (n : ℕ) → Funcsₘ ([] , Codeₛ)
%%   loadₘ  : (v : Var) → Funcsₘ ([] , Codeₛ)
%%   addₘ   : Funcsₘ ([] , Codeₛ)
%%   seqₘ   : Funcsₘ (Codeₛ ∷ Codeₛ ∷ [] , Codeₛ)

%% Σₘ : Signature
%% Σₘ = record  { sorts = Sortsₘ
%%              ; funcs = Funcsₘ
%%              }

%% CodeAlg : Algebra Σₘ
%% CodeAlg = ∣T∣ Σₘ
%% \end{spec}

%% \noindent La expresión $push\;3;load\;``x'';add$ del lenguaje target se corresponde con

%% \begin{spec}
%%   term seqₘ  (term (pushₘ 3) ⟨⟩ ▹
%%              (term seqₘ  (term (loadₘ `` x '') ⟨⟩ ▹
%%                          term add ⟨⟩ ▹
%%                          ⟨⟩)) ▹
%%              ⟨⟩)
%% \end{spec}

%% \noindent en el álgebra de términos |CodeAlg|.

%% \subsection{Semántica}

%% Las semánticas de ambos lenguajes las definimos a partir de álgebras
%% de las signaturas, obteniendo un homomorfismo desde el álgebra de términos.

%% \subsubsection*{Semántica del lenguaje source}

%% La semántica del lenguaje source para cada expresión es una función
%% que va de un estado en un natural. El setoide de estas funciones podemos
%% definirlo con la función |→-setoid| de la librería estándar, y será
%% la interpretación del sort |ExprN|.

%% \begin{spec}
%% State : Set
%% State = Var → ℕ

%% iSortsₑ : ISorts Σₑ
%% iSortsₑ ExprN = State →-setoid ℕ

%% if : ∀ {ar} {s} →  (f : funcs Σₑ (ar , s)) →
%%                    VecH Sortsₑ (Carrier ∘ iSortsₑ) ar →
%%                    Carrier (iSortsₑ s)
%% if (valN n) ⟨⟩           = λ σ → n
%% if plus (v₀ ▹ v₁ ▹ ⟨⟩) σ = v₀ σ + v₁ σ
%% if (varN x) ⟨⟩           = λ σ → σ x

%% iFuncsₑ : ∀ {ty} → (f : funcs Σₑ ty) → IFuncs Σₑ ty iSortsₑ
%% iFuncsₑ f = record  { _⟨$⟩_ = if f
%%                     ; cong = ... }

%% Semₑ : Algebra Σₑ
%% Semₑ = iSortsₑ ∥ iFuncsₑ

%% hSem : Homomorphism ExprAlg Semₑ
%% hSem = ∣T∣ₕ Semₑ
%% \end{spec}

%% De esta forma el valor semántico para la expresión $3 \oplus ``x''$ será:

%% \begin{spec}
%%   ′ hSem ′ ExprN ⟨$⟩ e = λ σ → 3
%% \end{spec}

%% \noindent donde |e = term plus (term (valN 3) ⟨⟩ ▹ term (varN `` x '') ⟨⟩ ▹ ⟨⟩)|.

%% \subsubsection*{Semántica del lenguaje target}

%% En el lenguaje target la semántica para cada expresión es una función parcial que va
%% de un par consistente de una ``pila'' de naturales y un estado de asignación
%% de valores a las variables (que llamaremos |Conf|), a otra pila. Esta función es parcial ya que la expresión $add$
%% puede ejecutarse sólamente si en la pila hay por lo menos dos elementos.
%% Implementaremos esta parcialidad utilizando el tipo |Maybe|:

%% \begin{spec}
%% data Stack : Set where
%%   ε   : Stack
%%   _▸_ : ℕ → Stack → Stack

%% Conf : Set
%% Conf = Stack × State


%% iSortsₘ : ISorts Σₘ
%% iSortsₘ Codeₛ = Conf →-setoid Maybe Stack


%% ifₘ : ∀ {ar} {s} →  (f : funcs Σₘ (ar , s)) →
%%                     VecH Sortsₘ (Carrier ∘ iSortsₘ) ar →
%%                     Carrier (iSortsₘ s)
%% ifₘ (pushₘ n) ⟨⟩  = λ {(s , σ) → just (n ▸ s)}
%% ifₘ (loadₘ v) ⟨⟩  = λ {(s , σ) → just (σ v ▸ s)}
%% ifₘ addₘ ⟨⟩       = λ  {  (n₀ ▸ n₁ ▸ s , σ)  → just (n₀ + n₁ ▸ s) ;
%%                           (_ , σ)            → nothing
%%                        }
%% ifₘ seqₘ (v₀ ▹ v₁ ▹ ⟨⟩) = λ {(s , σ) → v₀ (s , σ) >>= λ s' → v₁ (s' , σ)}


%% iFuncsₘ : ∀ {ty} → (f : funcs Σₘ ty) → IFuncs Σₘ ty iSortsₘ
%% iFuncsₘ f = record  { _⟨$⟩_ = ifₘ f
%%                     ; cong = ... }

%% Exec : Algebra Σₘ
%% Exec = iSortsₘ ∥ iFuncsₘ

%% hexec : Homomorphism CodeAlg Exec
%% hexec = ∣T∣ₕ Exec
%% \end{spec}

%% Como ejemplo consideremos el término

%% \begin{spec}
%% c = term seqₘ  (term (pushₘ 3) ⟨⟩ ▹
%%                (term seqₘ  (term (loadₘ `` x '') ⟨⟩ ▹
%%                            term add ⟨⟩ ▹
%%                            ⟨⟩)) ▹
%%                ⟨⟩)
%% \end{spec}


%% \noindent su semántica se obtendrá con el homomorfismo |hexec|:

%% \begin{spec}
%%   ′ hexec ′ Codeₛ ⟨$⟩ c = λ {(s , σ) → just (σ " x " + 3 ▸ s)
%% \end{spec}


%% \subsection{Traducción}

%% Tenemos los lenguajes source y target definidos con sus respectivas
%% semánticas. Podemos graficarlo en el siguiente diagrama:

%% \begin{diagram}
%%   |ExprAlg|     &     &   &  &    &|CodeAlg|\\
%%   \dTo_{|hSem|} &     &   &  &   &\dTo_{|hexec|}\\
%%   |Semₑ|        &     &   &  &    &|Exec|\\
%% \end{diagram}


%% Para poder traducir correctamente un lenguaje a otro según el framework que
%% presentamos, necesitamos llevar |CodeAlg| y |Exec| a la signatura |Σₑ|. Para ello definimos
%% una \textbf{traducción}. Como tenemos un sólo sort en cada lenguaje hay una
%% única opción para definir la traducción de sorts: |ExprN| se traduce
%% en |Codeₛ|.
%% La traducción de símbolos de función dará las reglas que se apliquen
%% cada vez que se deban interpretar los símbolos de |Σₑ| en una |Σₘ|-álgebra.
%% Estas reglas siguen las ideas para definir el compilador intuitivamente,
%% como lo mostramos previamente:

%% \begin{align*}
%%   comp\;n  &= push\;n\\
%%   comp\;v  &= load\;v\\
%%   comp\;e_1 \oplus e_2 &= comp\;e_1 ; comp\;e_2 ; add
%% \end{align*}


%% \subsubsection*{Traducción de la signatura}

%% \begin{spec}
%% sₑ↝sₘ : sorts Σₑ → sorts Σₘ
%% sₑ↝sₘ ExprN = Codeₛ

%% fₑ↝fₘ : ∀ {ar} {s} →  (f : funcs Σₑ (ar , s)) →
%%                       ΣExpr Σₘ (map sₑ↝sₘ ar) (sₑ↝sₘ s)
%% fₑ↝fₘ (valN n)  = pushₘ n ∣$∣ ⟨⟩
%% fₑ↝fₘ plus      = seqₘ ∣$∣  (# (suc zero) ▹
%%                             (seqₘ ∣$∣ ((# zero) ▹ (addₘ ∣$∣ ⟨⟩) ▹ ⟨⟩)) ▹
%%                             ⟨⟩)
%% fₑ↝fₘ (varN v)  = loadₘ v ∣$∣ ⟨⟩

%% ΣₑtoΣₘ : Σₑ ↝ Σₘ
%% ΣₑtoΣₘ = record { ↝ₛ = sₑ↝sₘ
%%                 ; ↝f = fₑ↝fₘ
%%                 }
%% \end{spec}

%% \subsubsection*{Transformación de las álgebras}

%% Habiendo definido la traducción |ΣₑtoΣₘ| podemos automáticamente
%% transformar cualquier |Σₘ|-álgebra en una |Σₑ|-álgebra.
%% Transformamos entonces |CodeAlg| y |Exec|:

%% \begin{spec}
%% CodeAlgₑ : Algebra Σₑ
%% CodeAlgₑ = ΣₑtoΣₘ 〈 CodeAlg 〉

%% Execₑ : Algebra Σₑ
%% Execₑ = ΣₑtoΣₘ 〈 Exec 〉
%% \end{spec}

%% \noindent y podemos llevar el homomorfismo |hexec| a la signatura
%% |Σₑ|:

%% \begin{spec}
%% hexecₑ : Homomorphism CodeAlgₑ Execₑ
%% hexecₑ = ΣₑtoΣₘ 〈 hexec 〉ₕ
%% \end{spec}

%% El compilador quedará definido por el único homomorfismo que existe
%% entre |ExprAlg| y |CodeAlgₑ|, ya que la primera de éstas es inicial:

%% \begin{spec}
%% homc : Homomorphism ExprAlg CodeAlgₑ
%% homc = ∣T∣ₕ CodeAlgₑ
%% \end{spec}


%% El diagrama ahora puede verse así:

%% \begin{diagram}
%%   |ExprAlg|     &\rTo^{|homc|}  &|CodeAlgₑ|\\
%%   \dTo_{|hSem|} &             &\dTo_{|hexecₑ|}\\
%%   |Semₑ|        &              &|Execₑ|\\
%% \end{diagram}

%% Para completar el diagrama necesitamos definir un homomorfismo entre
%% |Semₑ| y |Execₑ| (o al revés). Veremos que para nuestro ejemplo
%% dar un homomorfismo de |Semₑ| a |Execₑ| ($Enc$ en la terminología
%% de \cite{janssen-98}) obtiene la corrección del compilador.

%% Este homomorfismo relaciona las semánticas de cada lenguaje. Puesto que la semántica
%% del lenguaje source es una función que dado un estado obtiene un natural, en la semántica
%% del lenguaje target corresponde con poner ese natural en el tope de la pila:

%% \begin{spec}
%% Sem→Execₑ : Semₑ ⟿ Execₑ
%% Sem→Execₑ ExprN =
%%          record  { _⟨$⟩_  = λ {fₑ (s , σ) → just (fₑ σ ▸ s)}
%%                  ; cong   =  λ {  {f₀} {f₁} f₀≈f₁ (s , σ) →
%%                                   cong (λ n → just (n ▸ s)) (f₀≈f₁ σ) }
%%                  }


%% condhₛₑₘ : ∀ {ty}  (f : funcs Σₑ ty) →
%%                    homCond Semₑ Execₑ Sem→Execₑ f
%% condhₛₑₘ (valN n) ⟨⟩          = λ _ → refl
%% condhₛₑₘ plus (f₀ ▹ f₁ ▹ ⟨⟩)  = λ _ → refl
%% condhₛₑₘ (varN v) ⟨⟩          = λ _ → refl

%% hₛₑₘ : Homomorphism Semₑ Execₑ
%% hₛₑₘ = record  { ′_′ = Sem→Execₑ
%%                ; cond = condhₛₑₘ }
%% \end{spec}

%% \noindent la prueba de condición de homomorfismo resulta trivial.

%% Ahora tenemos que el siguiente diagrama conmuta, por inicialidad de |ExprAlg|:

%% \begin{diagram}
%%   |ExprAlg|     &\rTo^{|homc|}  &|CodeAlgₑ|\\
%%   \dTo_{|homSem|} &             &\dTo_{|hexecₑ|}\\
%%   |Semₑ|        &\rTo^{|hₛₑₘ|}  &|Execₑ|\\
%% \end{diagram}

%% \subsection{Extracción de la prueba de corrección}

%% Veamos cómo podemos obtener la prueba de corrección del compilador
%% a partir del desarrollo presentado.

%% El lenguaje de expresiones está definido a partir del álgebra de términos
%% |ExprAlg|:

%% \begin{spec}
%% Expr : Set
%% Expr = Carrier (ExprAlg ⟦ ExprN ⟧ₛ)
%% \end{spec}

%% El resultado de compilar expresiones serán los elementos del álgebra |CodeAlgₑ|:

%% \begin{spec}
%% Code : Set
%% Code = Carrier (CodeAlgₑ ⟦ ExprN ⟧ₛ)
%% \end{spec}

%% La función semántica del lenguaje source está definida por el homomorfismo |hSem|, y podemos dar una sintaxis
%% más sencilla:

%% \begin{spec}
%% ⟦_⟧_ : Expr → State → ℕ
%% ⟦ e ⟧ σ = (′ hSem ′ ExprN ⟨$⟩ e) σ
%% \end{spec}

%% Podemos hacer lo mismo para la semántica del lenguaje target:

%% \begin{spec}
%% ⟪_⟫ : Code → Conf → Maybe Stack
%% ⟪ c ⟫ = ′ hexecₑ ′ ExprN ⟨$⟩ c
%% \end{spec}


%% El compilador está definido por el homomorfismo |homc|:

%% \begin{spec}
%% compₑ : Expr → Code
%% compₑ e = ′ homc ′ ExprN ⟨$⟩ e 
%% \end{spec}

%% La prueba de corrección del compilador expresa que si compilamos una expresión y
%% ejecutamos el código resultante a partir de la pila |s| y un estado |σ|, el
%% resultado será la pila |s| con el valor semántico de la expresión agregado en el tope:


%% \begin{spec}
%% correct : ∀  (e : Expr) → (s : Stack) → (σ : State) → 
%%              ⟪ compₑ e ⟫ (s , σ) ≡ just ((⟦ e ⟧ σ) ▸ s)
%% \end{spec}

%% A partir del framework algebraico se puede extraer esta prueba:

%% \begin{spec}
%% correct e s σ = (elim≈ₕ unic ExprN e e refl) (s , σ)
%%   where  unic : (hexecₑ ∘ₕ homc) ≈ₕ (hₛₑₘ ∘ₕ homSem)
%%          unic = unique (∣T∣init Σₑ) Execₑ (hexecₑ ∘ₕ homc) (hₛₑₘ ∘ₕ homSem)
%% \end{spec}

%% El desarrollo completo del ejemplo puede verse en |Ejemplos/CorrectC.agda|, en \cite{univAlgebra}.
