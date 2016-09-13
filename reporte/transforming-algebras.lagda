\section{Transformación de álgebras}
\label{sec:trans}

Con todo lo formalizado en la sección anterior podemos definir los lenguajes
source y target como álgebras de términos de dos signaturas, sus dominios
semánticos como álgebras, y las funciones semánticas como homomorfismos, que son
únicos por inicialidad.

El enfoque algebraico para definir un traductor correcto se basa en poder
ver al lenguaje target y su semántica, como álgebras de la signatura source.

Para ver cómo pueden transformarse álgebras de una signatura a otra consideremos
el ejemplo del compilador de expresiones. Tenemos los lenguajes $Expr$ y
$Code$ que pueden definirse a partir de dos signaturas:

\begin{itemize}

\item $\Sigma_e$, con un único sort $E$ y símbolos de función:
  \begin{itemize}
    \item Para cada $n \in \mathds{N}$, $val\,n$, cuyo tipo es $[] \rightarrow E$
    \item Para cada $v \in Var$, $var\,v$, con tipo $[] \rightarrow E$
    \item $plus$, con tipo $[E , E] \rightarrow E$.
  \end{itemize}
\item $\Sigma_m$, con un único sort $C$ y símbolos de función:
  \begin{itemize}
    \item Para cada $n \in \mathds{N}$, $push\,n$, cuyo tipo es $[] \rightarrow C$
    \item Para cada $v \in Var$, $load\,v$, con tipo $[] \rightarrow C$
    \item $seq$, con tipo $[C , C] \rightarrow C$
    \item $add$, con tipo $[] \rightarrow C$
  \end{itemize}
\end{itemize}  

A partir de estas signaturas tenemos sus álgebras de términos $T(\Sigma_e)$ y
$T(\Sigma_m)$ que representan la sintaxis de ambos lenguajes.

También podemos definir las semánticas a partir de dos álgebras $Sem$ y $Exec$ de
cada signatura respectivamente, con los homomorfismos $h_{sem} : T(\Sigma_e) \rightarrow Sem$ y
$h_{exec} : T(\Sigma_m) \rightarrow Exec$ que están definidos por inicialidad del álgebra de términos.

\begin{diagram}
  T_(\Sigma_e)     &     &   &  &    &T_(\Sigma_m)\\
  \dTo_{hSem}  &     &   &  &   &\dTo_{hExec}\\
  Sem         &     &   &  &    &Exec\\
\end{diagram}


Podríamos definir una $\Sigma_e$-álgebra $T_m\sim$ donde la interpretación del sort $E$ sean
los términos del álgebra de términos $T\,(\Sigma_m)$ de la siguiente manera:

\begin{itemize}
  \item $val_{T_m\sim}\,n$ $=$ $push\,n$, para cada $n \in \mathds{N}$.
  \item $var_{T_m\sim}$  $=$ $load\,v$, para cara $v \in Var$.
  \item $plus_{T_m\sim}\,c_1\,c_2$ $=$ $seq\,c_1\,(seq\,c_2\,add)$.
\end{itemize}

\noindent y podríamos también definir una $\Sigma_e$-álgebra $Exec\sim$ así:

\begin{itemize}
  \item $val_{Exec\sim}\,n$ $=$ $push_{Exec}\,n$, para cada $n \in \mathds{N}$.
  \item $var_{Exec\sim}$  $=$ $load_{Exec}\,v$, para cara $v \in Var$.
  \item $plus_{Exec\sim}\,c_1\,c_2$ $=$ $seq_{Exec}\,c_1\,(seq\,c_2\,add_{Exec})$.
\end{itemize}

De hecho podríamos definir cualquier $\Sigma_e$-álgebra $A\sim$ a partir de una
$\Sigma_m$-álgebra $A$: Al carrier $E$ lo interpretamos con $C_{A}$. Al símbolo
constante $val\,n$ lo interpretamos $push_{A}\,n$, al símbolo $var\,v$ con
$load_{A}\,v$ y a $plus$, con la función que lleva dos elementos
$a_1, a_2 \in C_{A}$ a $seq_{A}\,a_1\,(seq_{A}\,a_2\,add_{A})$.

Es decir que podemos transformar cualquier $\Sigma_m$-álgebra a la signatura
$\Sigma_e$ teniendo definido para cada sort de $\Sigma_e$, un sort de $\Sigma_m$,
y reglas que nos indiquen cómo interpretar un símbolo de función de $\Sigma_e$ combinando
símbolos de $\Sigma_m$, en este caso teníamos:

\begin{itemize}
  \item[sorts] $E \rightsquigarrow C$
  \item[operaciones]
    \begin{itemize}
      \item $val\,n \rightsquigarrow push\,n$
      \item $var\,v \rightsquigarrow load\,v$
      \item $plus \rightsquigarrow seq\,\#0\,(seq\,\#1\,add)$
    \end{itemize}  
\end{itemize}

\noindent En el caso de la interpretación de $plus$, teníamos que aplicar la interpretación
de $seq$ a los argumentos de la función. Podemos dar la regla general indicando a qué
argumento nos referimos. En este caso indicamos que debe aplicarse $seq$ al primer argumento
y a la aplicación de $seq$ al segundo argumento y el símbolo $add$.

Podemos definir en agda cómo dar estas reglas que nos indiquen cómo interpretar
los sorts y símbolos de una signatura $\Sigma_s$ con sorts y símbolos de
una signatura $\Sigma_t$, y lo llamaremos \textit{traducción de signaturas}.
Este concepto se corresponde con la noción de \textit{derived signature morphism} en
\cite{sannella2012foundations}. Teniendo definida una traducción de signaturas podemos
transformar cualquier $\Sigma_t$-álgebra en una $\Sigma_e$-álgebra.





%% \cite{sannella2012foundations}

%% y $\Sigma_m$. Podríamos
%% definir una $\Sigma_e$-álgebra que tenga como carrier del único sort a los términos
%% de $\Sigma_m$.



%% El framework de traducción algebraico que presentamos se basa en, viendo
%% a los lenguajes como álgebras de términos 

%% como álgebras de términos de una signatura

%% poder probar la corrección
%% de un traductor utilizando el resultado de que el álgebra de términos
%% de una signatura es inicial, es decir, que existe un único homomorfismo
%% entre ésta y cualquier otra álgebra. El

%% Los lenguajes fuente y target pueden definirse mediante signaturas, y sus
%% semánticas a partir de álgebras de estas. 



%% Con el desarrollo algebraico presentado en la sección anterior se puede
%% probar la corrección de un traductor de lenguajes.

%% Un lenguaje puede definirse a partir de una signatura. Los sorts se corresponden
%% con las distintas categorías sintácticas del lenguaje, y los símbolos de función
%% con constructores (las constantes son símbolos de función con aridad vacía).
%% Los términos del lenguaje para un sort $S$ serán los elementos del carrier de sort
%% $S$ en el álgebra de términos.

%% El problema de traducir expresiones de un lenguaje $L_s$ en expresiones de un lenguaje
%% $L_t$ puede verse desde un enfoque algebraico. La sintaxis de los lenguajes está
%% definida por las signaturas y sus correspondientes álgebras de términos. La semántica
%% queda definida por álgebras junto con los homomorfismos dados por inicialidad del álgebra
%% de términos:

%% \begin{diagram}
%%   T_s     &     &   &  &    &T_t\\
%%   \dTo_{hSem_s} &     &   &  &   &\dTo_{hSem_t}\\
%%   Sem_s        &     &   &  &    &Sem_t\\
%% \end{diagram}

%% A una función que lleve expresiones del lenguaje fuente al target la llamamos
%% traductor.
%% Si podemos transformar las álgebras $T_t$ y $Sem_t$ en álgebras de la signatura $\Sigma_s$
%% (es decir, interpretar los sorts y símbolos de función de $\Sigma_s$ en los carriers de dichas
%% álgebras), al homomorfismo $hSem_t$ como un homomorfismo entre estas álgebras transformadas (digamos
%% $\theta(T_t)$, $\theta(Sem_t)$ y $\theta(hSem_t)$) y si damos un homomorfismo $Enc$ o $Dec$ entre $Sem_s$
%% y $\theta(Sem_t)$, el traductor quedará definido por el único homomorfismo que hay entre $T_s$ y
%% $\theta(T_t)$, y su corrección por la conmutación del diagrama resultante, gracias a la inicialidad
%% de $T_s$:

%% \begin{diagram}
%%   T_s     &\rTo^{trad}  &\theta(T_t)\\
%%   \dTo_{hSem_s} &          &\dTo_{\theta(hSem_t)}\\
%%   Sem_s        &\pile{\rTo^{Enc} \\ \lTo{Dec}}  &\theta(Sem_t)\\
%% \end{diagram}

%% Podemos definir cada álgebra transformada, interpretando los sorts y los símbolos de función
%% en los carriers correspondientes. Sin embargo este trabajo sería repetitivo y deberíamos hacerlo
%% para cada álgebra de la signatura $\Sigma_t$ que querramos transformar. También deberíamos redefinir
%% los homomorfismos, probando que se preserva la condición al cambiar de signatura.

%% En lugar de hacer eso, definiremos un (meta)lenguaje para traducir cualquier álgebra de una signatura en otra.

\subsection*{Traducción de signaturas}

Dadas dos signaturas $\Sigma_s$ y $\Sigma_t$, una traducción $\Sigma_s \rightsquigarrow \Sigma_t$ consiste
de un mapeo de sorts de $\Sigma_s$ en sorts de $\Sigma_t$, y de reglas para traducir símbolos de función.

Estas reglas asignan para cada símbolo de función una \textit{expresión} en la que pueden ocurrir símbolos
de función de la signatura $\Sigma_t$ aplicados según su aridad. Dada una aridad $[s_0,...,s_n]$
de una signatura $\Sigma$, definimos la familia $\Sigma Expr$ indexada en los sorts de $\Sigma$:

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


