\section{Algebra transformation}
\label{sec:trans}

With all definitions formalized in the previous section we can define signatures
for the languages source, and the semantics are obtained by initiality, interpreting
sorts and function symbols.

The main aspect of algebraic approach to correct translation is being able to
conceive both languages, source and target, as algebras of source signature.

Let's consider an example to introduce the ideas. We have languages $Expr$ and
$Code$ defined by the following signatures:

\begin{itemize}

\item $\Sigma_e$, with a sort $E$ and operations:
  \begin{itemize}
    \item For each $n \in \mathds{N}$, $val\,n$, with type $[] \rightarrow E$.
    \item For each $v \in Var$, $var\,v$, with type $[] \rightarrow E$.
    \item $plus$, with type $[E , E] \rightarrow E$.
  \end{itemize}
\item $\Sigma_m$, with a sort $C$ and operations:
  \begin{itemize}
    \item For each $n \in \mathds{N}$, $push\,n$, with type $[] \rightarrow C$.
    \item For each $v \in Var$, $load\,v$, with type $[] \rightarrow C$.
    \item $seq$, with type $[C , C] \rightarrow C$.
    \item $add$, with type $[] \rightarrow C$.
  \end{itemize}
\end{itemize}  

The semantics can be defined by algebras, say $Sem$ and $Exec$, of each signature respectively and
there are unique homomorphisms from the term algebras to each one: $h_{sem} : T(\Sigma_e) \rightarrow Sem$,
$h_{exec} : T(\Sigma_m) \rightarrow Exec$. 

\begin{center}
  \begin{tikzpicture}[>=latex]
    \node (te) at (0,2) {$T_e$}; 
    \node (tc) at (4,2) {$T_c$}; 
    \node (seme) at (0,0) {$\mathit{Sem}$} ; 
    \node (semc) at (4,0) {$\mathit{Exec}$} ; 
    \path [->,shorten <=2pt,shorten >=2pt] (te) edge node [left] {$\mathit{hsem}$} (seme); 
    \path [->,shorten <=2pt,shorten >=2pt] (tc) edge node [right] {$\mathit{hexec}$} (semc);
  \end{tikzpicture}
\end{center}

%\begin{diagram}
%  T_(\Sigma_e)     &     &   &  &    &T_(\Sigma_m)\\
%  \dTo_{hSem}  &     &   &  &   &\dTo_{hExec}\\
%  Sem         &     &   &  &    &Exec\\
%\end{diagram}

We could define a $\Sigma_e$-algebra $\hat{T_m}$ where the interpretation of sort $E$ is the
set of terms of the term algebra $T(\Sigma_m)$ and the interpretation of operations is defined
in the following way:

\begin{itemize}
  \item $val_{T_m\sim}\,n$ $=$ $push\,n$, for each $n \in \mathds{N}$.
  \item $var_{T_m\sim}$  $=$ $load\,v$, for each $v \in Var$.
  \item $plus_{T_m\sim}\,c_1\,c_2$ $=$ $seq\,c_1\,(seq\,c_2\,add)$.
\end{itemize}

\noindent and we could define a $\Sigma_e$-algebra $\hat{Exec}$:

\begin{itemize}
  \item $val_{Exec\sim}\,n$ $=$ $push_{Exec}\,n$, for each $n \in \mathds{N}$.
  \item $var_{Exec\sim}$  $=$ $load_{Exec}\,v$, for each $v \in Var$.
  \item $plus_{Exec\sim}\,c_1\,c_2$ $=$ $seq_{Exec}\,c_1\,(seq\,c_2\,add_{Exec})$.
\end{itemize}

Indeed, we can define any $\Sigma_e$-algebra $\hat{\mathcal{A}}$ from a $\Sigma_m$-algebra
$\mathcal{A}$: The interpretation of sort $E$ is $C_{\mathcal{A}}$. Operation
$val\,n$ is interpreted with $(push\,n)_{\mathcal{A}}$, symbol $var\,v$ with $(load\,v)_{\mathcal{A}}$
and $plus$ with a function that takes two elements $a_1, a_2 \in C_{\mathcal{A}}$ and
returns $seq_{\mathcal{A}}\,a_1\,(seq_{\mathcal{A}}\,a_2\,add_{\mathcal{A}})$.

So, we can transform a $\Sigma_m$-algebra to a $\Sigma_e$-algebra if we have
a translation of sorts of $\Sigma_e$ in sorts of $\Sigma_m$, and rules for interpreting
each function symbol of $\Sigma_e$ combining function symbols of $\Sigma_m$. In our
example we have:

\begin{itemize}
  \item[sorts] $E \rightsquigarrow C$
  \item[operations]
    \begin{itemize}
      \item $val\,n \rightsquigarrow push\,n$
      \item $var\,v \rightsquigarrow load\,v$
      \item $plus \rightsquigarrow seq\,\#0\,(seq\,\#1\,add)$
    \end{itemize}  
\end{itemize}

\noindent For interpretation of $plus$ we have to apply the interpretation
of $seq$ to the arguments of the function. We can give a general rule indicating
the arguments with natural numbers. In this case, $seq$ is apply to the first argument,
and the application of $seq$ to the second arguement and $add$ symbol.

Let's define in Agda "Signature translation", concept that is known in the bibliography
as \textit{polynomial derivor}, \cite{janssen-98} or \textit{derived signature morphism}
in \cite{mossakowski-15}.

\subsection*{Signature translation}

Let $\Sigma_s$ y $\Sigma_t$ be two signatures, a translation $\Sigma_s \rightsquigarrow \Sigma_t$ consists
of a map of sorts of $\Sigma_s$ in sorts of $\Sigma_m$, and rules for translating function symbols.
This rules consists of asigning each operation to an \textit{expression} in which can occur function
symbols of signature $\Sigma_t$, applied according to the arity.



\begin{itemize}
  \item Sea $i$, tal que $0 \leq i \leq n$,
    \begin{center}
      $\#i \in \Sigma Expr_{s_i}$
    \end{center}
  \item Sea $g$ una operación de $\Sigma$ con tipo $[s'_0,...,s'_m] \rightarrow s$, y
        sean $e_0 \in \Sigma Expr_{s'_0}$ , ... , $e_m \in \Sigma Expr_{s'_m}$,
        \begin{center}
          $g\,\$\,(e_0,...,e_m) \in \Sigma Expr_{s}$
        \end{center}
\end{itemize}
  
Para traducir entonces un símbolo de función $f$ de $\Sigma_s$ con tipo $[s_0,...,s_n] \rightarrow s$,
damos una $\Sigma Expr$ de la signatura $\Sigma_t$ con aridad $[s_0\rightsquigarrow,...,s_n\rightsquigarrow]$
(donde cada $s_i\rightsquigarrow$ es el resultado de mapear el sort $s_i$ de acuerdo a la traducción) y sort
$s\rightsquigarrow$.

Podemos definir en Agda el tipo $\Sigma Expr$:


%% Sea |ts : sorts↝|, si tenemos un símbolo de función |f| en |Σₛ| con tipo |([sˢ₁,...,sˢₙ] , s)|, daremos una regla
%% que permita interpretar al símbolo |f| en un álgebra |A| definida para la signatura |Σₜ|.
%% La interpretación de |f| es una función que va de un vector |⟨v₁,...,vₙ⟩|, donde cada |vᵢ| pertenece
%% a la interpretación en |A| del sort |(ts sˢᵢ)|, a un elemento en la interpretación en |A| del sort
%% |(ts s)|.
%% Podemos dar una regla que diga cómo definir esta interpretación para cualquier |Σₜ|-álgebra. Al símbolo
%% |f| lo traducimos a una expresión consistente de combinar símbolos de función de |Σₜ| de manera que respeten
%% el tipo de |f|. En esta expresión pueden ocurrir referencias a los parámetros de la interpretación de la función
%% o aplicación de símbolos de función en la signatura target a un vector de expresiones, donde también podrán
%% ocurrir referencias a parámetros.
%% Damos una definición recursiva para estas expresiones, que llamamos |ΣExpr|:

\begin{spec}
data ΣExpr (Σ : Signature) (ar : Arity Σ) : (sorts Σ) → Set where
  #      : (n : Fin (length ar)) → ΣExpr Σ ar (ar ‼ n)
  _∣$∣_   : ∀ {ar'} {s} → (f : funcs Σ (ar' , s)) →
             (es : VecH (sorts Σ) (ΣExpr Σ ar) ar') → ΣExpr Σ ar s
\end{spec}

Un elemento |e : ΣExpr Σ ar s| será una expresión en la cual pueden ocurrir
referencias a parámetros correspondiéndose con la aridad |ar| y el sort resultante
es |s|. La expresión |e| puede ser una referencia al parámetro |i|-ésimo (|# i|), en cuyo
caso |s| será igual a |(ar ‼ i)|. O puede ser la aplicación de un símbolo de función con alguna aridad
|ar'| y sort |s|, aplicado a un vector de |ΣExpr|.

La traducción de signaturas la definimos con un record parametrizado en las
signaturas source y target, conteniendo un campo para la traducción de sorts y
otro para la traducción de símbolos de función:

\begin{spec}
record _↝_ (Σₛ : Signature) (Σₜ : Signature) : Set where
  field
    ↝ₛ  : sorts Σₛ → sorts Σₜ
    ↝f : ∀ {ar} {s} →  (f : funcs Σₛ (ar , s)) →
                       ΣExpr Σₜ (map ↝ₛ ar) (↝ₛ s)
\end{spec}


%%Un ejemplo de |ΣExpr| podría ser el siguiente:

%% \medskip
%% \noindent Sean
%% \begin{spec}
%% Σ : Signature

%% s₁ s₂ s₃ s : sorts Σ

%% ar = s₁ ∷ s₂ ∷ [ s₃ ]

%% ar' = s₂

%% g : funcs Σ (ar' , s)
%% \end{spec}

%% \noindent Podemos definir:

%% \begin{spec}
%% e : ΣExpr Σ ar s
%% e = g ∣$∣ (# (suc zero))
%% \end{spec}

%% \noindent La expresión |e| representa una regla para definir una interpretación,
%% la cual consistirá de aplicar la interpretación de la operación |g| al segundo
%% argumento. Observemos que la única forma posible de escribir estas reglas es con
%% los tipos correctos.

%%Definamos entonces la traducción de signaturas:


%% \noindent Para traducir una signatura debemos definir una traducción de sorts |↝ₛ| y
%% una traducción de símbolos de función, que consiste en asignar para cada símbolo |f| de
%% la signatura |Σₛ| con tipo |(ar , s)|, una |ΣExpr| de |Σₜ| donde cada sort es traducido con
%% la función |↝ₛ|.

\paragraph{Ejemplo}

Veamos un ejemplo de traducción, donde la signatura source corresponde a la lógica proposicional
con los conectivos ``conjunción'' y ``negación'', la constante ``True'' y variables proposicionales;
y la signatura target corresponde a la lógica proposicional con
los conectivos ``disyunción'' y ``negación'', la constante ``False'' y las variables
proposicionales.


\begin{spec}
data Sₛ : Sorts where
  bool : Sₛ

data Fₛ : Funcs Sₛ where
  varₛ   : (v : Var) → Fₛ ([] , bool)
  trueₛ  : Fₛ ([] , bool)
  andₛ   : Fₛ (bool ∷ [ bool ] , bool)
  negₛ   : Fₛ ([ bool ] , bool)

Σₛ : Signature
Σₛ = record { sorts = Sₛ ; funcs = Fₛ }
\end{spec}

\begin{spec}
Sₜ : Sorts
Sₜ = Sₛ

data Fₜ : Funcs Sₜ where
  varₜ   : (v : Var) → Fₜ ([] , bool)
  falseₜ : Fₜ ([] , bool)
  orₜ    : Fₜ (bool ∷ [ bool ] , bool)
  negₜ   : Fₜ ([ bool ] , bool)

Σₜ : Signature
Σₜ = record { sorts = Sₜ ; funcs = Fₜ }
\end{spec}

Para dar la traducción tenemos que dar una función de los sorts de |Σₛ| en
los sorts de |Σₜ|. Como en este caso coinciden, es simplemente la identidad:

\begin{spec}
sₛ↝sₜ : sorts Σₛ → sorts Σₜ
sₛ↝sₜ = id
\end{spec}

Y ahora damos la traducción de los símbolos de función. En el caso de las
variables y la negación, tenemos el símbolo en la signatura target. Para el caso
de la constante |trueₛ| la traducción consiste en aplicar negación sobre la constante
|falseₜ|, y para traducir la conjunción utilizamos la regla de De Morgan:

\begin{center}
  $a \wedge b = \neg ((\neg a) \vee (\neg b))$
\end{center}


\begin{spec}
fₛ↝fₜ : ∀ {ar} {s} →  (f : funcs Σₛ (ar , s)) →
                      ΣExpr Σₜ (map sₛ↝sₜ ar) (sₛ↝sₜ s)
fₛ↝fₜ (varₛ v)  = varₜ v ∣$∣ ⟨⟩
fₛ↝fₜ trueₛ     = negₜ ∣$∣ ((falseₜ ∣$∣ ⟨⟩) ▹ ⟨⟩)
fₛ↝fₜ negₛ      = negₜ ∣$∣ ((# zero) ▹ ⟨⟩)
fₛ↝fₜ andₛ      = negₜ ∣$∣  (orₜ ∣$∣  ((negₜ ∣$∣ ((# zero) ▹ ⟨⟩)) ▹
                                      ((negₜ ∣$∣ ((# (suc zero)) ▹ ⟨⟩))
                                      ▹ ⟨⟩))
                            ▹ ⟨⟩)
\end{spec}

Finalmente la traducción de las signaturas será:

\begin{spec}
ΣₛtoΣₜ : Σₛ ↝ Σₜ
ΣₛtoΣₜ = record  { ↝ₛ = sₛ↝sₜ
                 ; ↝f = fₛ↝fₜ
                 }
\end{spec}

\subsection*{Transformación de álgebras}

Teniendo una traducción $\Sigma_s \rightsquigarrow \Sigma_t$, podemos definir
una $\Sigma_s$-álgebra a partir de una $\Sigma_t$-álgebra. Llamaremos
\textit{álgebra transformada} a la $\Sigma_s$-álgebra obtenida por una traducción.
Este concepto se corresponde con \textit{reduct algebra w.r.t. a derived signature morphism}
en \cite{sannella2012foundations}.

Sea $t$ una traducción $\Sigma_s \rightsquigarrow \Sigma_t$, y sea $\mathcal{A}$ una $\Sigma_t$-álgebra,
queremos definir una $\Sigma_s$-álgebra $\mathcal{A}\sim$. 

\begin{itemize}
  \item Para cada sort $s$ de $\Sigma_s$, $\mathcal{A}\sim_{s} = \mathcal{A}_{(t\,s)}$
  \item Para cada $f$, operación de $\Sigma_s$, con tipo $[s_0,...,s_n] \rightarrow s$,
        y sea $t\,f\,= e$, se define la interpretación
        \begin{align*}
          &f_{\mathcal{A}\sim} : \mathcal{A}\sim_{s_0} \times ... \times \mathcal{A}\sim_{s_n} \rightarrow \mathcal{A}\sim_s\\
          &f_{\mathcal{A}\sim}\,(a_1,...,a_n)\,=\,\mathbf{i}\,e\\
        \end{align*}
        \noindent donde $\mathbf{i}$ se define recursivamente:
    \begin{itemize}
    \item Si $e = \#j$, con $0 \leq j \leq n$,
      \begin{center}
        $\mathbf{i}\,e$ $=$ $a_j$
      \end{center}

    \item Si $e = g\,(e_1,...,e_m)$, donde $g$ es un símbolo de función de $\Sigma_t$ y $e_1,...,e_m$
          son $\Sigma$Expr con sorts de acuerdo a la aridad de $g$,
          \begin{center}
            $\mathbf{i}\,e$ $=$ $g_{\mathcal{A}}\,(\mathbf{i}\,e_1,...,\mathbf{i}\,e_m)$
          \end{center}
    \end{itemize}
\end{itemize}

Para formalizar la interpretación de símbolos de función en un álgebra
transformada, definimos |iFun↝|, que captura la idea que explicamos previamente.
Si |e| es la expresión correspondiente a la traducción de la operación |f| de |Σₛ|,
Dada una |Σₜ|-álgebra |a|, |iFun↝ f e a| obtiene la interpretación de |f| en la
transformación de |a|:

\begin{spec}
iFun↝ : ∀  {Σₛ Σₜ : Signature} {ar : Arity Σₛ}
           {s : sorts Σₛ} {fs↝ : sorts Σₛ → sorts Σₜ} →
           (f : funcs Σₛ (ar , s)) → (e : ΣExpr Σₜ (map fs↝ ar) (fs↝ s)) →
           (a : Algebra Σₜ) → IFuncs Σₛ (ar , s) (_⟦_⟧ₛ a ∘ fs↝)
iFun↝ = ...
\end{spec}

\noindent La definición contiene pequeñas dificultades técnicas y por ello no la incluimos
en este texto.

Podemos ahora definir la formalización de transformación de álgebras:

\begin{spec}
_〈_〉 : ∀ {Σₛ} {Σₜ} → (t : Σₛ ↝ Σₜ) →
        (a : Algebra Σₜ) → Algebra Σₛ
_〈_〉 t a =  (_⟦_⟧ₛ a ∘ ↝ₛ t) ∥
            (λ f → iFun↝ f (↝f t f) a)
\end{spec}

A partir de una traducción |t : Σₛ ↝ Σₜ| y un álgebra |a : Algebra Σₜ| obtenemos
una |Σₛ|-álgebra |t 〈 a 〉|.

Por último, también podemos ver un homomorfismo entre dos $\Sigma_t$-álgebras
$\mathcal{A}$ y $\mathcal{A'}$ como un homomorfismo entre las dos $\Sigma_s$-álgebras
transformadas. La siguiente definición formaliza este concepto, y se corresponde
con \textit{reduct homomorphism w.r.t. a derived signature morphism} en
\cite{sannella2012foundations}.

\begin{spec}
_〈_〉ₕ : ∀  {Σₛ Σₜ : Signature} {a a' : Algebra Σₜ} →
             (t : Σₛ ↝ Σₜ) → (h : Homomorphism a a') →
             Homomorphism (t 〈 a 〉) (t 〈 a' 〉)
t 〈 h 〉ₕ = record  { ′_′ = ′ h ′ ∘ ↝ₛ t
                   ; cond = ...
                   }
\end{spec}





%% Sean |sˢ₁,...,sˢₙ| y |fˢ₁,...,fˢₖ| los sorts y símbolos de función de |Σₛ|;
%% |sᵗ₁,...,sᵗₘ| y |fᵗ₁,...,fᵗⱼ| los sorts y símbolos de función de |Σₜ|;
%% y |t : Σₛ ↝ Σₜ|. A partir de una |Σₜ|-álgebra |A| podemos definir una
%% |Σₛ|-álgebra de la siguiente manera:

%% \begin{itemize}
%%   \item Interpretamos a cada sort |sˢᵢ| con |a ⟦ ↝ₛ t sˢᵢ ⟧|.
%%   \item Para cada símbolo de función |fˢᵢ| con aridad |arᵢ|, definimos la interpretación de la siguiente manera:
%%     \begin{itemize}
%%     \item Si |↝f t fˢᵢ| es |# h|, con |h : Fin (length arᵢ)| definiremos la interpretación
%%           \begin{spec}
%%             ifˢᵢ vs = vs ‼ h
%%           \end{spec}
%%     \item Si |↝f t fˢᵢ| es |g ∣$∣ ⟨ e₁ , ... , eₚ ⟩ |, donde |g : funcs Σₜ ar' s'| y |e₁ , ... , eₚ| son
%%           |ΣExpr|:
%%           \begin{spec}
%%             ifˢᵢ vs = A ⟦ g ⟧ ⟨$⟩ ies
%%           \end{spec}

%%           donde |ies| es el vector resultante de interpretar cada expresión |e₁,...,eₚ|, y posiblemente
%%           ocurran elementos de |vs|.
%%     \end{itemize}
%% \end{itemize}

%% Con estas ideas intuitivas podemos definir formalmente la transformación de álgebras. No mostraremos
%% los detalles, pueden encontrarse en el archivo |AlgTransf.agda|, en \cite{univAlgebra}.

%% \begin{spec}
%% _〈_〉 : ∀  {Σ₀} {Σ₁} → (t : Σ₀ ↝ Σ₁) →
%%             (a : Algebra Σ₁) → Algebra Σ₀
%% t 〈 a 〉 =  (_⟦_⟧ₛ a ∘ ↝ₛ t) ∥
%%            (λ f → iFun↝ f (↝f t f) a)
%% \end{spec}

%% \noindent La definición de |iFun↝| formaliza la idea intuitiva explicada previamente.

%% Tenemos entonces que a partir de una traducción |t : Σₛ ↝ Σₜ| y una |Σₜ|-álgebra A podemos
%% obtener una |Σₛ|-álgebra, y esta es t 〈 A 〉.

%% Podremos también transformar un homomorfismo |h| entre dos |Σₜ|-álgebras |A| y |A'| a un homomorfismo
%% entre |t 〈 A 〉| y |t 〈 A' 〉|, cuya notación será |t 〈 h 〉ₕ|. Los detalles también se pueden ver en
%% (CITA).


