\documentclass[a4paper,twoside,12pt]{article}
\usepackage{amsmath}
\usepackage{mathpartir}
\usepackage[small,nohug,heads=vee]{diagrams}
\diagramstyle[labelstyle=\scriptstyle]
\usepackage{authblk}
\usepackage{ dsfont }
\usepackage{ upgreek }
\usepackage{ hyperref }
%include agda.fmt
%include unicode.fmt

\begin{document}

\title{Formalización de un framework algebraico para
       traducción correcta de lenguajes}

\author{Emmanuel Gunther}
\affil{FaMAF, UNC}
\affil{CONICET}

\date{}
       
\maketitle

\begin{abstract}

  Un enfoque para abordar el desarrollo de traductores correctos de lenguajes es mediante
  álgebras universales. En este trabajo presentamos una formalización en teoría de tipos
  de un framework algebraico para traducir lenguajes, realizado en el lenguaje
  Agda. Para ello definimos conceptos básicos de álgebras universales heterogéneas, como
  Signatura, Álgebra, Homomorfismo, llegando a probar que el álgebra de términos es inicial.
  Definimos también un metalenguaje para traducir signaturas de manera general y damos un
  ejemplo de un compilador de expresiones a un lenguaje de máquina sencillo que manipula
  un stack.

\end{abstract}

\section{Introducción}

El desarrollo de compiladores correctos es un tema de interés en Ciencias de la Computación
que se ha estudiado desde épocas tempranas. Morris (\cite{morris-73}) presentó un esquema
en el cual propone utilizar álgebras universales heterogéneas (\cite{birkhoff-70}) para probar la corrección
de un compilador, trabajo que luego extendió Thatcher (\cite{thatcher-80}). En
\cite{janssen-98} se realiza un análisis de los distintos trabajos existentes en el momento
con el objetivo de dar un esquema general para la traducción de lenguajes (no sólo lenguajes
de programación, sino que abarca distintas áreas). En este trabajo formalizamos un framework
similar al que propone Janssen.
El enfoque se basa en considerar la sintaxis abstracta de un lenguaje como el álgebra inicial
de una signatura multisort, y a cualquier otra álgebra como un posible dominio semántico,
teniendo definido por inicialidad un único homomorfismo (la semántica). El grupo conocido
como ADJ presentan esta manera de ver la sintaxis y semántica de los lenguajes en \cite{goguen-77}.

Introduzcamos un ejemplo sencillo para explicar el enfoque que formalizaremos, un compilador
de expresiones aritméticas en un código de máquina que manipula un stack.

\paragraph{Lenguaje fuente}
El lenguaje fuente son expresiones aritméticas simples: constantes, variables y suma. 

\begin{quote}
$ Expr  ::=  \;\; Nat  \;\; || \;\;  Var \;\; || \;\; Expr ⊕ Expr $
\end{quote}

\paragraph{Lenguaje target}
El lenguaje target es un código de máquina cuya ejecución manipulará una pila de números naturales. 

\begin{quote}
$ Code  ::=  \;\; push\,Nat  \;\; || \;\; load\, Var \;\; || \;\; Code \,;\, Code \;\; || \;\; add $
\end{quote}

\noindent En ambos casos, $Nat$ corresponde a las constantes naturales y $Var$ a variables.


\paragraph{Semántica fuente}
La semántica del lenguaje fuente podemos definirla como una función que asigna a cada expresión
una función que va de un estado de asignación de valores a variables, a un natural:

\begin{align*}
  &eval     :\;Expr \rightarrow State \rightarrow \mathds{N}\\
  &eval\;n \;=\; \lambda\,\upsigma \rightarrow n\\
  &eval\;v \;=\;\lambda\,\upsigma \rightarrow \upsigma\,v\\
  &eval\;(e_1 \oplus e_2)\;=\;\lambda\,\upsigma \rightarrow (eval\,e_1\,\upsigma) + (eval\,e_1\,\upsigma)\\
\end{align*}

\paragraph{Semántica target}
La semántica del lenguaje target asignará a cada código una función que va de un par consistente de un estado
y una pila, a otra pila. Podemos representar la pila con una lista de naturales:

\begin{align*}
  &exec     :\;Code \rightarrow State \times Stack \rightarrow Stack\\
  &exec\;(push\,n) \;=\; \lambda\,(\upsigma , s) \rightarrow (s : n)\\
  &exec\;(load\,v) \;=\;\lambda\,(\upsigma , s) \rightarrow (\upsigma\,v\,:\,s)\\
  &exec\;(c_1\,;\,c_2)\;=\;\lambda\,(\upsigma , s) \rightarrow exec\;c_2\;(\upsigma,exec\;c_1\;(\upsigma,s))\\
\end{align*}

\paragraph{Compilador}
El compilador llevará expresiones en $Expr$ a códigos en $Code$:

\begin{align*}
  &comp     :\;Expr \rightarrow Code\\
  &comp\;n \;=\; push\,n\\
  &comp\;v \;=\;load\,v\\
  &comp\;(e_1 \oplus e_2)\;=\;comp\,e_2\,;\,comp\,e_1\,;\,add\\
\end{align*}

\paragraph{Corrección}
Este compilador es correcto si se puede probar:
    \begin{center}
      $exec\,(comp\,e)\,(\upsigma,s)\,=\,eval\,e\,:\,s$
    \end{center}

En el enfoque que presentamos los lenguajes están definidos a partir
de dos signaturas $\Sigma_e$ y $\Sigma_c$, obteniendo sus álgebras de términos
$T_e$ y $T_c$. Los dominios semánticos, digamos $Sem$ y $Exec$, serán álgebras de
cada signatura respectivamente. En el primer caso cada elemento del carrier
del álgebra $Sem$ será una función con tipo $State \rightarrow \mathds{N}$, en el
segundo una función con tipo $State \times Stack \rightarrow Stack$. Las semánticas
quedan determinadas por el único homomorfismo que existe entre el álgebra de términos
y cada álgebra, por inicialidad. Tenemos entonces el siguiente diagrama:

\begin{diagram}
  T_e     &     &   &  &    &T_c\\
  \dTo_{hsem} &     &   &  &   &\dTo_{hexec}\\
  Sem      &     &   &  &    &Exec\\
\end{diagram}

La clave del enfoque consiste en poder ver a las álgebras (y homomorfismos) de la signatura $\Sigma_c$
como álgebras (y homomorfismos) de la signatura fuente $\Sigma_e$, para ello introduciremos
el concepto de \textit{transformador de álgebras} (similar a \textit{polynomial derivor},
que nombra Janssen, o \textit{derived signature morphism} en teoría de instituciones, \cite{mossakowski-15}).
Si $A$ es una $\Sigma_c$-álgebra, llamemos $A\sim$ a su transformada en $\Sigma_e$. Tenemos
entonces el siguiente diagrama:

\begin{diagram}
  T_e     &\rTo^{comp}    &T_c\sim\\
  \dTo_{hsem} & &\dTo_{hexec\sim}\\
  Sem      &  &Exec\sim\\
\end{diagram}

El compilador queda definido por el único homomorfismo que existe entre $T_e$ y $T_c\sim$.
Si podemos definir un homomorfismo $enc$ (o $dec$) entre $Sem$ y $Exec\sim$ (o viceversa), el diagrama conmuta
por inicialidad de $T_e$:

\begin{diagram}
  T_e     &\rTo^{comp}    &T_c\sim\\
  \dTo_{hsem} & &\dTo_{hexec\sim}\\
  Sem      & \pile{\rTo^{enc} \\ \lTo_{dec}}   &Exec\sim\\
\end{diagram}

\paragraph{Organización del texto}

En la segunda sección de este artículo formalizamos los conceptos de signatura, álgebra,
homomorfismo, inicialidad y álgebra de términos, obteniendo
una librería en Agda para el uso de álgebras universales en general. Se discuten
algunas decisiones de implementación. El resultado es similar al que obtiene
Venanzio Capretta en \cite{capretta-99}.

En la tercera sección introducimos el concepto de transformación de álgebras,
para llevar álgebras de la signatura target a la signatura source,
y probamos que los homomorfismos se preservan. Este concepto no está
en la bibliografía existente sobre formalización de álgebras universales.

En la cuarta sección damos el ejemplo completo del compilador de un lenguaje
de expresiones aritméticas simple presentado anteriormente, utilizando el
framework.

\section{Álgebras Universales}

Presentamos una formalización de los conceptos de álgebra universal necesarios para
probar que el álgebra de términos es inicial, en el lenguaje Agda.

\paragraph{Agda}
Agda es un lenguaje de programación funcional con tipos dependientes, basado
en la teoría de tipos intuicionista de Martin Löf. ...

En el presente texto mostraremos las principales definiciones de la formalización,
omitiendo algunos detalles técnicos. Puede encontrarse el texto completo en
\url{https://git.cs.famaf.unc.edu.ar/semantica-de-la-programacion/algebras-universales/UnivAlgebra.agda}.

Las definiciones que formalizamos están basadas en el \textit{Handbook of Logic in Computer Science}, (\cite{handbook}).

\subsection{Signatura, álgebra y homomorfismo}

\subsection*{Signatura}

%if False
\begin{code}

module reporte where

open import Relation.Binary
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Nat renaming (_⊔_ to _⊔ₙ_)
open import Data.Product renaming (map to pmap)
open import Function
open import Function.Equality renaming (_∘_ to _∘ₛ_)
open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open import Data.String
open import Data.Fin

open import VecH

open Setoid

\end{code}
%endif

Una \textbf{signatura} es un par $(S,F)$ de conjuntos, el primero llamado \textit{sorts} y el segundo
\textit{operaciones} (también llamados \textit{símbolos de función}). Una operación es una tripla
$(w,[s_1,...,s_n],s)$ consistente de un nombre, una lista de sorts y un sort, usualmente escrito como
$(w : [s_1,...,s_n] \rightarrow s)$. Llamaremos \textit{aridad} a la lista de sorts $[s_1,...,s_n]$, \textit{target sort} al sort $s$ y
$tipo$ al par $([s_1,...,s_n],s)$. \footnote{En la bibliografía sobre álgebras heterogéneas varía
  la noción de aridad. En el handbook se denomina aridad a lo que aquí llamamos tipo, y sorts argumento
  a lo que aquí llamamos aridad.}

Formalizamos el concepto de signatura en Agda definiendo un record con dos campos. |sorts| es cualquier
tipo y |funcs| una familia indexada en los tipos de las operaciones:

\begin{code}
Sorts : Set _
Sorts = Set

Funcs : Sorts → Set _
Funcs S = (List S) × S → Set
 
record Signature : Set₁ where
  field
    sorts  : Sorts
    funcs  : Funcs sorts

  Arity : Set
  Arity = List sorts

  Type : Set
  Type = List sorts × sorts
\end{code}

Una ventaja de tener definido de esta forma la signatura es que el mismo sistema
de tipos de Agda nos permite definir propiedades sólo para las operaciones
de determinada aridad. Es decir, podemos expresar con un tipo en Agda a las operaciones
de una signatura que tengan determinado tipo. Este enfoque es más type-theorético y veremos
algunas ventajas importantes al definir la traducción de signaturas.

En una implementación donde se define a las operaciones como una lista de tipos
(como en \cite{capretta-99}) sería bastante más complicado definir una propiedad
restringiendo el tipo de la operación. También notemos que podemos tener una signatura con
infinitas operaciones, como veremos en un ejemplo.

\paragraph{Ejemplo 1} Veamos un ejemplo de un lenguaje de
expresiones naturales y booleanas, para notar el uso de varios sorts. 

\begin{code}
data S : Sorts where
  bool : S
  nat  : S

data F : Funcs S where
  fzero  : F ([] , nat)
  fsuc   : F ([ nat ] , nat)
  ftrue  : F ([] , bool)
  ffalse : F ([] , bool)
  feq    : F (nat ∷ [ nat ] , bool)

Σ₁ : Signature
Σ₁ = record  { sorts = S
             ; funcs = F
             }
\end{code}

\paragraph{Ejemplo 2} El segundo ejemplo es el lenguaje de expresiones aritméticas que presentamos en la introducción
y para el cual daremos un compilador.

\begin{spec}
Var : Set
Var = String  
  
data Sortsₑ : Sorts where
  ExprN : Sortsₑ

data Funcsₑ : Funcs Sortsₑ where
  valN  : (n : ℕ) → Funcsₑ ([] , ExprN)
  plus  : Funcsₑ ( ExprN ∷ [ ExprN ] , ExprN )
  varN  : (v : Var) → Funcsₑ ([] , ExprN)


Σₑ : Signature
Σₑ = record  { sorts = Sortsₑ
             ; funcs = Funcsₑ
             }
\end{spec}

\noindent Notemos que en este último ejemplo tenemos infinitos símbolos de función, uno por
cada natural (el constructor |valN|), y uno por cada variable (el constructor |varN|).

\subsection*{Álgebra}

Dada una signatura $\Sigma$, un \textbf{álgebra} $\mathcal{A}$ de $\Sigma$ (o una $\Sigma$-álgebra)
consta de una familia de conjuntos indexada en los sorts de $\Sigma$ llamado los
\textit{carriers} (o \textit{interpretación de sorts}) de $\mathcal{A}$ (llamaremos $\mathcal{A}_s$ al carrier del sort $s$), y para cada operación
$w$ con tipo $[s_1,...,s_n],s$ una función total $w_A : \mathcal{A}_{s_1} \times ... \times \mathcal{A}_{s_n} \rightarrow \mathcal{A}_s$.
Llamaremos \textit{interpretación} de $w$ a esta función.

Para definir el carrier de un sort consideremos primero como ejemplo el álgebra correspondiente al dominio semántico del
lenguaje de expresiones que introdujimos previamente. Habíamos visto que para
cada expresión damos una función que va de un estado de asignación a variables en
un natural. Es decir que cada elemento del carrier del álgebra será una función.
Una dificultad que tenemos con estos conjuntos en Agda es para definir la igualdad
de dos elementos. Decimos que dos funciones son iguales, si lo son punto a punto,
lo que se conoce como \textit{igualdad extensional}. Sin embargo en Agda dos funciones
que tengan esta propiedad no son iguales proposicionalmente (debería explicar qué es esta igualdad),
por lo cual si para implementar los carriers utilizamos Sets, dos funciones extensionalmente iguales
no serán el mismo elemento.

Por esta razón necesitamos contar con un tipo más general que los Sets, de manera de poder definir,
además del tipo de los elementos que lo conforman, la relación de igualdad. Para ello
utilizamos \textbf{Setoides}.

\paragraph{Setoides} Aquí explicaré setoides.

%% Para implementar los carriers de las álgebras utilizamos setoides.
%% Un setoide es un tipo que tiene definido una relación de equivalencia sobre sus elementos:

%% \begin{spec}
%% record Setoid c ℓ : Set (suc (c ⊔ ℓ)) where
%%   infix 4 _≈_
%%   field
%%     Carrier       : Set c
%%     _≈_           : Rel Carrier ℓ
%%     isEquivalence : IsEquivalence _≈_
%% \end{spec}

%% El |Carrier| del setoide es el tipo de los elementos que lo componen y |_≈_|
%% una relación binaria sobre el carrier. También se requiere la prueba de que esta
%% relación es de equivalencia.
%% Dados dos setoides $S_1$ y $S_2$ se define el tipo $S_1 \longrightarrow S_2$, que
%% consiste de la función que va del carrier de $S_1$ al carrier de $S_2$ (cuya notación
%% en Agda será con el símbolo |_⟨$⟩_|) y una prueba de que conserva la relación de igualdad,
%% es decir, si $s_1$ |≈|$_{S_1}$ $s_1'$ entonces $f \, s_1$ |≈|$_{S_2}$ $f \, s_1'$
%% (|cong|, en Agda).

%% Una diferencia importante entre usar setoides en lugar de |Sets| es que podemos tener
%% carriers de álgebras con una noción de igualdad que no sea simplemente la igualdad
%% proposicional. Por ejemplo, se puede definir el setoide de las funciones de |A| en |B|,
%% donde la igualdad subyacente sea la extensional, probando que es una relación de equivalencia.
%% También fácilmente se podrían definir álgebras cocientes.

\noindent Definimos entonces la interpretación de sorts (o carriers) en una $\Sigma-$-álgebra:

\begin{code}
ISorts : ∀ {ℓ₁ ℓ₂} → (Σ : Signature) → Set _
ISorts {ℓ₁} {ℓ₂} Σ = (sorts Σ) → Setoid ℓ₁ ℓ₂
\end{code}

\noindent Un elemento en |ISorts Σ s| será un setoide, y representa la interpretación del sort
|s| en una |Σ|-álgebra.

Para interpretar un símbolo de función $f$, con tipo $[s_1,...,s_n] \rightarrow s$ tendremos que
definir una función que tome como parámetros elementos de la interpretación de cada sort $s_i$,
y devuelva un elemento en la interpretación de $s$. Para definir el tipo de los parámetros
de la función utilizaremos vectores. Notemos que estos vectores contendrán elementos de distintos
tipos, de acuerdo a la interpretación de los sorts según la aridad. Definimos entonces
el tipo de los \textit{vectores heterogéneos}:

\paragraph{Vectores heterogéneos} blablabla

%% Dado un tipo $T$ indexado en $I$, y una lista de índices $[i_1,...,i_n]$,
%% un vector heterogéneo es una colección de $n$ elementos, donde cada uno es de
%% tipo $T\,i$:

%% \begin{spec}
%% data VecH (I : Set) (A : I -> Set _) : List I → Set _ where
%%   ⟨⟩  : VecH I A []
%%   _▹_ : ∀ {i} {is} → (v : A i) → (vs : VecH I A is) → VecH I A (i ∷ is)
%% \end{spec}

%% Dada una familia de relaciones $R$ indexada en un tipo $I$, podemos definir la
%% relación de dos vectores extendiendo $R$. Nos referiremos a esta extensión con
%% el símbolo |~v|. Si la relación es la correspondiente a la de un setoide para
%% cada elemento |i : I| de una lista |is|, podemos definir el setoide de los
%% vectores heterogéneos:

%% \begin{spec}
%% VecSet :  ∀ {ℓ₁ ℓ₂} → (I : Set) → (A : I → Setoid ℓ₁ ℓ₂) →
%%           List I → Setoid _ _
%% VecSet = ...
%% \end{spec}

%% El carrier de este setoide es el tipo de los vectores con índices en |I|, lista de índices
%% |is| y elementos en |Carrier (A i)|, donde cada |i| es un elemento de |is|.
%% La relación de equivalencia es la extensión a vectores de la familia de relaciones |_≈_ ∘ A|.

%% En \cite{vecH} está implementada la librería de vectores heterogéneos con estas definiciones
%% y más propiedades del tipo.

Definimos entonces la interpretación de operaciones. Dada una operación $f$ con tipo
$ty$, y dada una interpretación de sorts $is$, la intepretación de $f$ se define como una función
entre el setoide de los vectores heterogéneos con los sorts de $\Sigma$ como índices, $is$ como
la familia indexada en los sorts de $\Sigma$ y la aridad de $f$ como lista de índices de cada
elemento:

\begin{code}
IFuncs :  ∀ {ℓ₁ ℓ₂} → (Σ : Signature) → (ty : ΣType Σ) →
          ISorts {ℓ₁} {ℓ₂} Σ → Set _
IFuncs Σ (ar , s) is = VecSet (sorts Σ) is ar ⟶ is s
\end{code}

\noindent Notemos que un elemento en |IFuncs Σ (ar , s) is| es una función entre setoides.

Finalmente definimos el tipo de las $\Sigma$-álgebras, como un record con dos campos, uno
correspondiente a la interpretación de los sorts, y el otro para los símbolos de función:

\begin{code}
record Algebra {ℓ₁ ℓ₂ : Level}  (Σ : Signature) :
                                Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  constructor _∥_
  field
    _⟦_⟧ₛ    : ISorts {ℓ₁} {ℓ₂} Σ
    _⟦_⟧    : ∀ {ty : ΣType Σ} → (f : funcs Σ ty) → IFuncs Σ ty _⟦_⟧ₛ
\end{code}

Utilizamos operadores como nombres de los campos para tener una sintaxis
más compacta. La interpretación del sort |s| en |A| se escribirá |A ⟦ s ⟧ₛ| y
la de una operación |w|, |A ⟦ w ⟧|.

Definamos también un tipo para el dominio de la función interpretación de una operación en una
|Σ|-álgebra |A|, que nos será útil en definiciones posteriores.
Si una operación tiene aridad |ar|, su interpretación será una función entre setoides, cuyo
dominio son los vectores heterogéneos con aridad |ar| e interpretación |_⟦_⟧ₛ A|.

\begin{spec}
_⟦_⟧ₛ* : ∀ {Σ} {ℓ₁} {ℓ₂} → (A : Algebra {ℓ₁} {ℓ₂} Σ) → (ar : Arity Σ) → Set _
_⟦_⟧ₛ* {Σ} A ar = Carrier (VecSet (sorts Σ) (_⟦_⟧ₛ A) ar)
\end{spec}

\medskip

Como ejemplo de la formalización de álgebra, definamos una para la signatura |Σₑ|, correspondiente
al lenguaje de expresiones aritméticas.

\paragraph{Ejemplo} Definamos la |Σₑ|-álgebra |Semₑ|, correspondiente al dominio
semántico del lenguaje de expresiones. Los elementos semánticos serán funciones
que van de estados en naturales. Al estado de asignación de variables lo podemos
implementar con funciones de |Var| en |ℕ|:

\begin{spec}
State : Set
State = Var → ℕ
\end{spec}

La interpretación del único sort |ExprN| es el setoide de las funciones de |State| en
|ℕ|. Con |→-setoid| podemos definir una función entre dos setoides triviales, donde la relación
de igualdad es la extensional:

\begin{spec}
iSortsₑ : ISorts Σₑ
iSortsₑ ExprN = State →-setoid ℕ
\end{spec}

Definamos la interpretación de cada símbolo de función, que será una función entre setoides.
Como vimos previamente, una función entre setoides tiene dos campos: la función entre sus carriers, y la
prueba de que preserva la igualdad. No mostraremos esta última.

Para cada |n : ℕ| tenemos un símbolo de función |valN n|. Esta operación tiene aridad vacía y target sort a
|ExprN|.

\begin{spec}
iValN : (n : ℕ) → IFuncs Σₑ ([] , ExprN) iSortsₑ
iValN n = record  { _⟨$⟩_ = λ { ⟨⟩ σ → n }
                  ; cong = ... }
\end{spec}

La operación |plus| tiene tipo |(ExprN ∷ [ ExprN ] , ExprN)|. Por lo tanto la interpretación
en el álgebra que queremos definir será una función que tome un vector de dos elementos
de tipo |State → ℕ| y devolverá otro elemento con tipo |State → ℕ|:

\begin{spec}
iPlus : IFuncs Σₑ (ExprN ∷ [ ExprN ] , ExprN) iSortsₑ
iPlus = record  { _⟨$⟩_ = λ { (v₀ ▹ v₁ ▹ ⟨⟩) σ → v₀ σ + v₁ σ }
                ; cong = ... }
\end{spec}

Por último, para cada variable |v| tenemos una operación |varN v|, con aridad vacía
y target sort |ExprN|. Su interpretación entonces, será una función que toma como parámetro
el vector vacío, y devuelve una función en |State → ℕ|. Su definición corresponde a aplicar
el estado a la variable |v|:

\begin{spec}
iVarN : (v : Var) → IFuncs Σₑ ([] , ExprN) iSortsₑ
iVarN v = record  { _⟨$⟩_ = λ { ⟨⟩ σ → σ v }
                  ; cong = ... }
\end{spec}

Podemos juntar estas tres definiciones para tener la interpretación de los símbolos
de función:

\begin{spec}
iFuncsₑ : ∀ {ty} → (f : funcs Σₑ ty) → IFuncs Σₑ ty iSortsₑ
iFuncsₑ (valN n) = iValN n
iFuncsₑ plus = iPlus
iFuncsₑ (varN v) = iVarN v
\end{spec}

Y definimos finalmente el álgebra |Semₑ|:

\begin{spec}
Semₑ : Algebra Σₑ
Semₑ = iSortsₑ ∥ iFuncsₑ
\end{spec}

\subsection*{Homomorfismo}

Dadas dos $\Sigma$-álgebras $A$ y $B$, un \textbf{homomorfismo} $h$ de $A$ a $B$
es una familia de funciones indexadas en los sorts de $\Sigma$, $h_s : A_s \rightarrow B_s$,
tal que para cada operación $w$ de $\Sigma$ con aridad $([s_1,...,s_n],s)$, se cumple:

\begin{center}
  $h_s(f_A(a_1,...,a_n)) = f_B(h_{s_1}\,a_1,...,h_{s_n}\,a_n)$ \;\;\;(1)
\end{center}

Definamos primero la noción de \textit{función entre} $\Sigma$\textit{-álgebras}. Dadas
dos $\Sigma$-álgebras $A$ y $B$, definimos la función entre ambas como una familia de funciones
indexada en los sorts de $\Sigma$ entre los carriers:

\begin{spec}
_⟿_ : ∀  {Σ : Signature}  →
         (A : Algebra Σ) → (A' : Algebra Σ) →
         Set _
_⟿_ {Σ} A A' = (s : sorts Σ) → A ⟦ s ⟧ₛ ⟶ A' ⟦ s ⟧ₛ
\end{spec}

\noindent Notemos que para cada sort tenemos una función entre los setoides
correspondientes a su interpretación en cada álgebra.

Procedamos ahora a definir la condición de homomorfismo. En la parte derecha de la ecuación (1) tenemos
la aplicación de la función $h$ en cada elemento de $(a_1,...,a_n)$. Definimos esta notación en Agda. Si
|ar| es una aridad y |A| una |Σ|-álgebra, definimos como mapear una función entre álgebras |h| a un
vector en |A ⟦ ar ⟧ₛ*|. A esta función la notaremos con |map⟿| y no pondremos en este texto
su definición.

%% Primero, dado un símbolo
%% de función $f$ con aridad $[s_1,...,s_n]$, la interpretación $f$ en una
%% $\Sigma$-álgebra $A$ toma como argumento vectores heterogéneos donde cada
%% elemento $a_i$ pertenece a la interpretación de $s_i$ en $A$. Definamos
%% el tipo de estos vectores para facilitar la notación. Sea |A| una $\Sigma$-álgebra
%% y |ar| una aridad de $\Sigma$:

%% \begin{spec}
%% idom : _
%% idom {Σ} ar A = VecH (sorts Σ) (Carrier ∘ _⟦_⟧ₛ A) ar
%% \end{spec}

%% En la parte derecha de la ecuación (1) tenemos la aplicación de la función $h$ en
%% cada elemento de $(a_1,...,a_n)$. Definimos esta notación en Agda, correspondiente
%% a ``mapear'' una función entre álgebras |h| a un vector en |idom ar A| (donde |ar|
%% es una aridad y |A| un álgebra), llamaremos a esta función |map⟿| (no daremos los
%% detalles).

A continuación damos la definición de un tipo para la condición de homomorfismo de
una función entre álgebras |h|. Si
|h : A ⟿ A'| y |f : funcs Σ (ar , s)|, para todo |(as : A ⟦ ar ⟧ₛ*)|, debe darse
la igualdad entre
la aplicación de |h| al resultado de aplicar la interpretación de |f| en |A| al vector
|as| y la aplicación de la interpretación de |f| en |A'| al resultado de mapear
|h| a |as|. La relación de igualdad correspondiente es la de la interpretación del sort
|s| en |A|:

\begin{spec}
homCond  A A' h f = (as : A ⟦ ar ⟧ₛ*) →  (h s ⟨$⟩ (A ⟦ f ⟧ ⟨$⟩ as))
                                         ≈ₛ 
                                         (A' ⟦ f ⟧ ⟨$⟩ (map⟿ h as))
         where  _≈ₛ_ : _
                _≈ₛ_ = _≈_ (A' ⟦ s ⟧ₛ) 
\end{spec}

Finalmente definimos \textbf{homomorfismo} con un record con dos campos: la función
entre álgebras y la condición de homomorfismo:

\begin{spec}
record Homomorphism (A : Algebra Σ) (A' : Algebra Σ) : Set _ where
  field
    ′_′    : A ⟿ A'
    cond   : ∀ {ty} (f : funcs Σ ty) → homCond A A' ′_′ f
\end{spec}

También en esta definición utilizamos una notación  más compacta para referirnos
a la función de un homomorfismo: |′ H ′|.

\subsection{Álgebra inicial y Álgebra de términos}

\subsection*{Álgebra inicial}

Una $\Sigma$-álgebra $A$ es llamada \textbf{inicial} si para toda otra
$\Sigma$-álgebra $B$, existe un único homomorfismo de $A$ a $B$.

Para formalizar este concepto tenemos que definir unicidad de un homomorfismo.
Informalmente podemos decir que un elemento $e \in A$ es único si para todo
otro elemento $e' \in A$ se da que $e = e'$. Podemos generalizar esta definición
a cualquier relación de equivalencia. El tipo |Unicity| expresa esta noción:

\begin{spec}
Unicity : ∀ {ℓ₁} {ℓ₂} →  (A : Set ℓ₁) → (rel : Rel A ℓ₂) →
                         IsEquivalence rel → Set _ 
Unicity A _≈_ p = Σ[ a ∈ A ] ((a' : A) → a ≈ a')
\end{spec}

Dado un tipo |A|, y una relación binaria |_≈_| entre elementos de |A|,
un |a : A| es único (salvo equivalencia) con respecto a |_≈_| si para todo otro elemento |a' : A|,
|a| y |a'| están relacionados.

Ahora deberíamos decir cuándo dos homomorfismos son iguales. La igualdad
que consideramos será la extensional: Dos funciones $f$ y $g$ son iguales si,
dados dos elementos $a$ y $b$ tales que $a = b$, entonces $f\,a = g\,b$.

Definamos la igualdad extensional en Agda, generalizando las relaciones de igualdad:

\begin{spec}
ExtProp _≈A_ _≈B_ f g = (a a' : A) → a ≈A a' → f a ≈B g a'
\end{spec}

Y ahora definamos un tipo que contenga las condiciones necesarias que deben cumplirse
para que dos homomorfismos sean extensionalmente iguales. Este tipo tendrá
un único constructor |ext| que expresa la propiedad de igualdad extensional
para la función del homomorfismo indexada en cada sort de la signatura:


\begin{spec}
data _≈ₕ_  {Σ} {A : Algebra Σ} {A' : Algebra Σ}
           (H H' : Homomorphism A A') : Set _ where
  ext :  ((s : sorts Σ) → ExtProp  (_≈_ (A ⟦ s ⟧ₛ)) (_≈_ (A' ⟦ s ⟧ₛ))
                                   (_⟨$⟩_ (′ H ′ s)) (_⟨$⟩_ (′ H' ′ s))) →
         H ≈ₕ H'
\end{spec}

Esta relación es de equivalencia. La prueba |equiv≈ₕ| lo demuestra, no damos
su definición por cuestiones de simplicidad:

\begin{spec}
equiv≈ₕ : ∀  {Σ} {A : Algebra Σ} {A' : Algebra Σ} →
              IsEquivalence (_≈ₕ_ {A = A} {A' = A'})
equiv≈ₕ = ...
\end{spec}

Con la relación igualdad de homomorfismos podemos expresar cuándo un homomorfismo
es único (salvo equivalencias) con respecto a ella. Definimos entonces álgebra inicial,
con un récord conteniendo el álgebra, y la prueba de que para toda otra álgebra hay
un único homomorfismo:

\begin{spec}
record Initial (Σ : Signature) : Set _ where
  field
    alg      : Algebra Σ
    init     : (A : Algebra Σ) → Unicity (Homomorphism alg A) (_≈ₕ_) equiv≈ₕ
\end{spec}


\subsection*{Álgebra de términos}

A partir de una signatura $\Sigma$ puede construirse un \textbf{álgebra de términos},
donde los elementos que conforman los carriers de cada sort $s$ son los términos generados por los
símbolos de función de $\Sigma$, con target sort $s$, también llamados \textit{ground terms}
o \textit{Herbrand Universe} de sort $s$ (que podemos escribir como $HU_s$):

\begin{itemize}
\item Sea $k$ una operación con tipo $[] \rightarrow s$, $k \in HU_s$
\item Si $f$ es una operación con tipo $[s_1,...,s_n] \rightarrow s$ y
      $t_i \in HU_{s_i}$ para cada $1 \leq i \leq n$, entonces $f\,(t_1,...,t_n) \in HU_s$
\end{itemize}

Podemos definir esta noción en Agda, con un tipo indexado en los sorts de la signatura,
con un único constructor |term| que tomará un símbolo de función y un vector de acuerdo a la aridad del mismo:


%% Estos carriers son llamados el \textit{Herbrand Universe}
%% de $\Sigma$. Como ejemplo, consideremos la signatura $\Sigma_1$, definida anteriormente,
%% la cual contenía dos sorts |bool| y |nat|. El carrier del álgebra de términos de $\Sigma_1$ para
%% el sort |nat| contiene a los elementos |fzero|, |fsuc fzero|, |fusc (fsuc fzero)|, etc.

%% Procedamos a definir el \textit{Herbrand Universe} de una signatura $\Sigma$ como un tipo indexado
%% en los sorts de $\Sigma$. Un elemento de este tipo será un término, que consta de un símbolo
%% de función y un vector heterogéneo donde cada elemento será un |HU| indexado en el sort correspondiente
%% a la aridad de la función:

\begin{spec}
data HU (Σ : Signature) : (s : sorts Σ) → Set where
  term : ∀ {ar} {s} →  (f : funcs Σ (ar , s)) →
                       (ts : VecH (sorts Σ) (HU Σ) ar) → HU Σ s
\end{spec}

Esta definición formaliza la definición de $HU_s$ que vimos previamente:

\begin{itemize}
\item Si |k : funcs Σ ([] , s)|, entonces |term k ⟨⟩ : HU Σ s|.
\item Si |f : funcs Σ ([s₁ ,..., sₙ] , s)| y |ts = ⟨ t_1,...,t_n ⟩|, donde
      |t₁ : HU Σ s₁|,...,|tₙ : HU Σ sₙ|, entonces |term f ts : HU Σ s|.
\end{itemize}

\paragraph{Ejemplo}
Consideremos como ejemplo algunos términos de la signatura |Σₑ|:

\begin{spec}
t₁ : HU Σₑ ExprN
t₁ = term (valN 2) ⟨⟩

t₂ : HU Σₑ ExprN
t₂ = term (varN " x ") ⟨⟩

t₃ : HU Σₑ ExprN
t₃ = term plus (t₁ ▹ t₂ ▹ ⟨⟩)
\end{spec}


Dada una signatura $\Sigma$ podemos definir un álgebra que tenga como carrier de cada sort
$s$ al conjunto $HU_s$ de manera trivial. La interpretación de cada símbolo de función
será el término en la familia $HU$ correspondiente. A esta álgebra se la suele escribir $T(\Sigma)$.
Podemos formalizarlo así:

%% El álgebra de términos de $\Sigma$ tendrá como carrier de un sort $s$ al Herbrand Universe
%% indexado en $s$. La igualdad de los elementos del carrier será la igualdad proposicional
%% (dos elementos son iguales sólo si lo son sintácticamente). La interpretación de un símbolo
%% de función |f| aplicado a un vector |vs| será el término |term f vs|:

\begin{spec}
∣T∣ : (Σ : Signature) → Algebra Σ
∣T∣ Σ = record  { _⟦_⟧ₛ = setoid ∘ HU Σ
               ; _⟦_⟧  = λ f → termFuns f
                }
  where termFuns f = record  { _⟨$⟩_ = term f
                             ; cong = ...
                             }
\end{spec}

\noindent Evitamos detallar en este texto la prueba de preservación de igualdad
de la función de interpretación por motivos de simplicidad.

Gracias a esta definición podemos entonces, a partir de cualquier signatura |Σ|, obtener
el álgebra de términos |∣T∣ Σ : Algebra Σ|. En lo que resta de esta sección explicaremos
la formalización de la prueba de que el álgebra de términos |∣T∣ Σ| es inicial.

\subsection*{El álgebra de términos es inicial}

Para probar que el álgebra de términos $T(\Sigma)$ es inicial debemos dar para toda
$\Sigma$-álgebra $\mathcal{A}$ un único homomorfismo de $T(\Sigma)$ a $\mathcal{A}$.

Podemos definir este homomorfismo de la siguiente forma: Sea $s$ un sort de $\Sigma$,

\begin{itemize}
\item Si $k$ es un símbolo de función constante con target sort $s$, luego
      $h\,k\,=\,k_{\mathcal{A}}$
\item Si $f$ es una operación con tipo $[s_1,...,s_n] \rightarrow s$, luego
      $h\,(f\,(t_1,...,t_n))\,=\,f_{\mathcal{A}}\,(h\,t_1,...,h\,t_n)$
\end{itemize}

Podríamos formalizar este homomorfismo así:

\begin{spec}
∣T∣→A : ∀ {A : Algebra Σ} (s : sorts Σ) → HU Σ s → Carrier (A ⟦ s ⟧ₛ)
∣T∣→A {A = A} s (term f ts) = A ⟦ f ⟧ ⟨$⟩ (mapV ∣T∣→A ts)
\end{spec}

\noindent sin embargo el chequeador de terminación de Agda no puede asegurar la terminación.
Lo resolvemos con dos funciones mutuamente recursivas donde vamos aplicando |∣T∣→A| en cada
elemento del vector:

\begin{spec}
mutual
  ∣T∣→A : ∀ {Σ} {A : Algebra Σ} (s : sorts Σ) → HU Σ s → Carrier (A ⟦ s ⟧ₛ)
  ∣T∣→A {A = A} s (term {[]} f ⟨⟩) = A ⟦ f ⟧ ⟨$⟩ ⟨⟩
  ∣T∣→A {A = A} s (term {s₀ ∷ _} f (t₀ ▹ ts)) =
                 A ⟦ f ⟧ ⟨$⟩ (∣T∣→A s₀ t₀) ▹ map∣T∣→A ts

  map∣T∣→A :  ∀ {Σ} {A : Algebra Σ} {ar : Arity Σ} →
              VecH (sorts Σ) (HU Σ) ar →
              VecH (sorts Σ) (Carrier ∘ _⟦_⟧ₛ A) ar
  map∣T∣→A {ar = []} ⟨⟩ = ⟨⟩
  map∣T∣→A {ar = s₁ ∷ _} (t₁ ▹ ts₁) = ∣T∣→A s₁ t₁ ▹ map∣T∣→A ts₁
\end{spec}

Esta definición pasa el chequeo de terminación de Agda y podríamos
probar que aplicar |map∣T∣→A| a un vector es igual a mapear |∣T∣→A| en
ese vector, de manera trivial.


Con la función |∣T∣→A| podemos definir entonces el homomorfismo entre
el álgebra de términos y cualquier otra álgebra (no mostramos la prueba
de la condición de homomorfismo ni la preservación de igualdad en el setoide):

\begin{spec}
∣T∣ₕ : ∀ {Σ} → (A : Algebra Σ) → Homomorphism (∣T∣ Σ) A
∣T∣ₕ A = record  { ′_′  = record  { _⟨$⟩_ = ∣T∣→A
                                  ; cong  = ...}
                 ; cond = ...}
\end{spec}

Finalmente sólo resta mostrar que este homomorfismo es único. Para ello, probamos
que dados dos homomorfismos |h₁| y |h₂| entre |∣T∣ Σ| y |A|, ambos son extensionalmente
iguales, es decir que |′ h₁ ′ s ⟨$⟩ term f ts| es igual a |′ h₂ ′ s ⟨$⟩ term f ts|, en el
setoide |A ⟦ s ⟧ₛ|, donde |f| es un símbolo de función con tipo |(ar , s)| y |ts| un
vector de |HU| indexado en cada elemento de |ar|. La prueba en Agda puede escribirse
así:

\begin{spec}
uni :  (h₁ : Homomorphism (∣T∣ Σ) A) →
       (h₂ : Homomorphism (∣T∣ Σ) A) →
       (s : sorts Σ) → (t₁ t₂ : HU Σ s) → t₁ ≡ t₂ →
       _≈_ (A ⟦ s ⟧ₛ) (′ h₁ ′ s ⟨$⟩ t₁) (′ h₂ ′ s ⟨$⟩ t₂)
uni h₁ h₂ s (term {ar} f ts) ._ refl =
                          begin
                            ′ h₁ ′ s ⟨$⟩ term f ts
                              ≈⟨ cond h₁ f ts ⟩
                            A ⟦ f ⟧ ⟨$⟩ (map⟿ ′ h₁ ′ ts)
                              ≈⟨ Π.cong (A ⟦ f ⟧) (mapV≡ ar ts) ⟩
                            A ⟦ f ⟧ ⟨$⟩ (map⟿ ′ h₂ ′ ts)
                              ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (cond h₂ f ts) ⟩ 
                            ′ h₂ ′ s ⟨$⟩ term f ts
                          ∎
                  where mapV≡ :  (ar : Arity Σ) → (ts₀ : VecH (sorts Σ) (HU Σ) ar) →
                                 (mapV (_⟨$⟩_ ∘ ′ h₁ ′) ts₀) ∼v
                                 (mapV (_⟨$⟩_ ∘ ′ h₂ ′) ts₀)
\end{spec}

\section{Transformación de álgebras}

Con el desarrollo algebraico presentado en la sección anterior se puede
probar la corrección de un traductor de lenguajes.

Un lenguaje puede definirse a partir de una signatura. Los sorts se corresponden
con las distintas categorías sintácticas del lenguaje, y los símbolos de función
con constructores (las constantes son símbolos de función con aridad vacía).
Los términos del lenguaje para un sort $S$ serán los elementos del carrier de sort
$S$ en el álgebra de términos.

El problema de traducir expresiones de un lenguaje $L_s$ en expresiones de un lenguaje
$L_t$ puede verse desde un enfoque algebraico. La sintaxis de los lenguajes está
definida por las signaturas y sus correspondientes álgebras de términos. La semántica
queda definida por álgebras junto con los homomorfismos dados por inicialidad del álgebra
de términos:

\begin{diagram}
  T_s     &     &   &  &    &T_t\\
  \dTo_{hSem_s} &     &   &  &   &\dTo_{hSem_t}\\
  Sem_s        &     &   &  &    &Sem_t\\
\end{diagram}

A una función que lleve expresiones del lenguaje fuente al target la llamamos
traductor.
Si podemos transformar las álgebras $T_t$ y $Sem_t$ en álgebras de la signatura $\Sigma_s$
(es decir, interpretar los sorts y símbolos de función de $\Sigma_s$ en los carriers de dichas
álgebras), al homomorfismo $hSem_t$ como un homomorfismo entre estas álgebras transformadas (digamos
$\theta(T_t)$, $\theta(Sem_t)$ y $\theta(hSem_t)$) y si damos un homomorfismo $Enc$ o $Dec$ entre $Sem_s$
y $\theta(Sem_t)$, el traductor quedará definido por el único homomorfismo que hay entre $T_s$ y
$\theta(T_t)$, y su corrección por la conmutación del diagrama resultante, gracias a la inicialidad
de $T_s$:

\begin{diagram}
  T_s     &\rTo^{trad}  &\theta(T_t)\\
  \dTo_{hSem_s} &          &\dTo_{\theta(hSem_t)}\\
  Sem_s        &\pile{\rTo^{Enc} \\ \lTo{Dec}}  &\theta(Sem_t)\\
\end{diagram}

Podemos definir cada álgebra transformada, interpretando los sorts y los símbolos de función
en los carriers correspondientes. Sin embargo este trabajo sería repetitivo y deberíamos hacerlo
para cada álgebra de la signatura $\Sigma_t$ que querramos transformar. También deberíamos redefinir
los homomorfismos, probando que se preserva la condición al cambiar de signatura.

En lugar de hacer eso, definiremos un (meta)lenguaje para traducir cualquier álgebra de una signatura en otra.

\subsection*{Traducción de signaturas}

Dadas dos signaturas $\Sigma_s$ y $\Sigma_t$, para llevar álgebras de $\Sigma_t$ en $\Sigma_s$ definimos
una \textit{traducción} de $\Sigma_s$ a $\Sigma_t$. Ésta consiste en una función que lleve sorts
de $\Sigma_s$ en $\Sigma_t$ y \textit{reglas} para traducir los símbolos de función.

\begin{spec}
sorts↝ : (Σₛ Σₜ : Signature) → Set
sorts↝ = sorts Σₛ → sorts Σₜ
\end{spec}

\noindent La traducción de sorts será una función entre los sorts de las signaturas.

Sea |ts : sorts↝|, si tenemos un símbolo de función |f| en |Σₛ| con tipo |([sˢ₁,...,sˢₙ] , s)|, daremos una regla
que permita interpretar al símbolo |f| en un álgebra |A| definida para la signatura |Σₜ|.
La interpretación de |f| es una función que va de un vector |⟨v₁,...,vₙ⟩|, donde cada |vᵢ| pertenece
a la interpretación en |A| del sort |(ts sˢᵢ)|, a un elemento en la interpretación en |A| del sort
|(ts s)|.
Podemos dar una regla que diga cómo definir esta interpretación para cualquier |Σₜ|-álgebra. Al símbolo
|f| lo traducimos a una expresión consistente de combinar símbolos de función de |Σₜ| de manera que respeten
el tipo de |f|. En esta expresión pueden ocurrir referencias a los parámetros de la interpretación de la función
o aplicación de símbolos de función en la signatura target a un vector de expresiones, donde también podrán
ocurrir referencias a parámetros.
Damos una definición recursiva para estas expresiones, que llamamos |ΣExpr|:

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

Un ejemplo de |ΣExpr| podría ser el siguiente:

\medskip
\noindent Sean
\begin{spec}
Σ : Signature

s₁ s₂ s₃ s : sorts Σ

ar = s₁ ∷ s₂ ∷ [ s₃ ]

ar' = s₂

g : funcs Σ (ar' , s)
\end{spec}

\noindent Podemos definir:

\begin{spec}
e : ΣExpr Σ ar s
e = g ∣$∣ (# (suc zero))
\end{spec}

\noindent La expresión |e| representa una regla para definir una interpretación,
la cual consistirá de aplicar la interpretación de la operación |g| al segundo
argumento. Observemos que la única forma posible de escribir estas reglas es con
los tipos correctos.

Definamos entonces la traducción de signaturas:

\begin{spec}
record _↝_ (Σₛ : Signature) (Σₜ : Signature) : Set where
  field
    ↝ₛ  : sorts Σₛ → sorts Σₜ
    ↝f : ∀ {ar} {s} → (f : funcs Σₛ (ar , s)) →
                        ΣExpr Σₜ (map ↝ₛ ar) (↝ₛ s)
\end{spec}

\noindent Para traducir una signatura debemos definir una traducción de sorts |↝ₛ| y
una traducción de símbolos de función, que consiste en asignar para cada símbolo |f| de
la signatura |Σₛ| con tipo |(ar , s)|, una |ΣExpr| de |Σₜ| donde cada sort es traducido con
la función |↝ₛ|.

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

Teniendo una traducción de una signatura |Σₛ| a otra |Σₜ|, podemos definir
una |Σₛ|-álgebra a partir de una |Σₜ|-álgebra.

Sean |sˢ₁,...,sˢₙ| y |fˢ₁,...,fˢₖ| los sorts y símbolos de función de |Σₛ|;
|sᵗ₁,...,sᵗₘ| y |fᵗ₁,...,fᵗⱼ| los sorts y símbolos de función de |Σₜ|;
y |t : Σₛ ↝ Σₜ|. A partir de una |Σₜ|-álgebra |A| podemos definir una
|Σₛ|-álgebra de la siguiente manera:

\begin{itemize}
  \item Interpretamos a cada sort |sˢᵢ| con |a ⟦ ↝ₛ t sˢᵢ ⟧|.
  \item Para cada símbolo de función |fˢᵢ| con aridad |arᵢ|, definimos la interpretación de la siguiente manera:
    \begin{itemize}
    \item Si |↝f t fˢᵢ| es |# h|, con |h : Fin (length arᵢ)| definiremos la interpretación
          \begin{spec}
            ifˢᵢ vs = vs ‼ h
          \end{spec}
    \item Si |↝f t fˢᵢ| es |g ∣$∣ ⟨ e₁ , ... , eₚ ⟩ |, donde |g : funcs Σₜ ar' s'| y |e₁ , ... , eₚ| son
          |ΣExpr|:
          \begin{spec}
            ifˢᵢ vs = A ⟦ g ⟧ ⟨$⟩ ies
          \end{spec}

          donde |ies| es el vector resultante de interpretar cada expresión |e₁,...,eₚ|, y posiblemente
          ocurran elementos de |vs|.
    \end{itemize}
\end{itemize}

Con estas ideas intuitivas podemos definir formalmente la transformación de álgebras. No mostraremos
los detalles, pueden encontrarse en el archivo |AlgTransf.agda|, en \cite{univAlgebra}.

\begin{spec}
_〈_〉 : ∀  {Σ₀} {Σ₁} → (t : Σ₀ ↝ Σ₁) →
            (a : Algebra Σ₁) → Algebra Σ₀
t 〈 a 〉 =  (_⟦_⟧ₛ a ∘ ↝ₛ t) ∥
           (λ f → iFun↝ f (↝f t f) a)
\end{spec}

\noindent La definición de |iFun↝| formaliza la idea intuitiva explicada previamente.

Tenemos entonces que a partir de una traducción |t : Σₛ ↝ Σₜ| y una |Σₜ|-álgebra A podemos
obtener una |Σₛ|-álgebra, y esta es t 〈 A 〉.

Podremos también transformar un homomorfismo |h| entre dos |Σₜ|-álgebras |A| y |A'| a un homomorfismo
entre |t 〈 A 〉| y |t 〈 A' 〉|, cuya notación será |t 〈 h 〉ₕ|. Los detalles también se pueden ver en
(CITA).



\section{Corrección de un compilador de expresiones}

En esta sección mostraremos la corrección de un compilador de un lenguaje
de expresiones naturales sencillo, a un lenguaje de máquina, que manipula un
stack.

El lenguaje fuente tiene la siguiente sintaxis:

\begin{quote}
$ e  ::=  \;\; n  \;\; || \;\;  v \;\; || \;\; e_1 ⊕ e_2 $
\end{quote}

\noindent donde $n$ es una constante natural y $v$ una variable.

La semántica de este lenguaje es la esperada, obteniendo un valor natural a partir
de un estado de asignación de valores a las variables.

\medskip

El lenguaje target tiene la siguiente sintaxis:

\begin{quote}
$ c  ::=  \;\; push\,n  \;\; || \;\; load\, v \;\; || \;\; c_1 ; c_2 \;\; || \;\; add $
\end{quote}

\noindent donde $n$ es una constante natural y $v$ una variable.

Informalmente, la ejecución de un código del lenguaje target modificará una pila de elementos
naturales utilizando también un estado de asignación de valores a las variables.
$push\,n$ pone en el tope de la pila el valor $n$; $load\,v$ pone en el tope de la pila el valor
de la variable $v$ en el estado; $c_1 ; c_2$ ejecuta $c_1$ y luego $c_2$ a partir del stack resultante;
y por último $add$ a partir de una pila que tiene al menos dos elementos en el tope, los quita de la pila
y pone el resultado de sumarlos.

El compilador lo definiríamos de esta forma:

\begin{align*}
  comp\;n  &= push\;n\\
  comp\;v  &= load\;v\\
  comp\;e_1 \oplus e_2 &= comp\;e_1 ; comp\;e_2 ; add
\end{align*}


Procedamos a definir este compilador de manera correcta utilizando el framework presentado
en las secciones anteriores.

\subsection{Sintaxis}

Podemos definir la sintaxis de ambos lenguajes a partir de dos signaturas |Σₑ| y |Σₘ|,
obteniendo las respectivas álgebras de términos:

\subsubsection*{Sintaxis del lenguaje source}

\begin{spec}
data Sortsₑ : Sorts where
  ExprN : Sortsₑ

data Funcsₑ : Funcs Sortsₑ where
  valN  : (n : ℕ) → Funcsₑ ([] , ExprN)
  plus  : Funcsₑ ( ExprN ∷ [ ExprN ] , ExprN )
  varN  : (v : Var) → Funcsₑ ([] , ExprN)


Σₑ : Signature
Σₑ = record  { sorts = Sortsₑ
             ; funcs = Funcsₑ
             }

ExprAlg : Algebra Σₑ
ExprAlg = ∣T∣ Σₑ

\end{spec}

\noindent La expresión $3 \oplus ``x''$ del lenguaje source se corresponde con

\begin{spec}
term plus (term (valN 3) ⟨⟩ ▹ term (varN `` x '') ⟨⟩ ▹ ⟨⟩)
\end{spec}

\noindent en el álgebra de términos |ExprAlg|.

\subsubsection*{Sintaxis del lenguaje target}

\begin{spec}
data Sortsₘ : Sorts where
  Codeₛ : Sortsₘ

data Funcsₘ : Funcs Sortsₘ where
  pushₘ  : (n : ℕ) → Funcsₘ ([] , Codeₛ)
  loadₘ  : (v : Var) → Funcsₘ ([] , Codeₛ)
  addₘ   : Funcsₘ ([] , Codeₛ)
  seqₘ   : Funcsₘ (Codeₛ ∷ Codeₛ ∷ [] , Codeₛ)

Σₘ : Signature
Σₘ = record  { sorts = Sortsₘ
             ; funcs = Funcsₘ
             }

CodeAlg : Algebra Σₘ
CodeAlg = ∣T∣ Σₘ
\end{spec}

\noindent La expresión $push\;3;load\;``x'';add$ del lenguaje target se corresponde con

\begin{spec}
  term seqₘ  (term (pushₘ 3) ⟨⟩ ▹
             (term seqₘ  (term (loadₘ `` x '') ⟨⟩ ▹
                         term add ⟨⟩ ▹
                         ⟨⟩)) ▹
             ⟨⟩)
\end{spec}

\noindent en el álgebra de términos |CodeAlg|.

\subsection{Semántica}

Las semánticas de ambos lenguajes las definimos a partir de álgebras
de las signaturas, obteniendo un homomorfismo desde el álgebra de términos.

\subsubsection*{Semántica del lenguaje source}

La semántica del lenguaje source para cada expresión es una función
que va de un estado en un natural. El setoide de estas funciones podemos
definirlo con la función |→-setoid| de la librería estándar, y será
la interpretación del sort |ExprN|.

\begin{spec}
State : Set
State = Var → ℕ

iSortsₑ : ISorts Σₑ
iSortsₑ ExprN = State →-setoid ℕ

if : ∀ {ar} {s} →  (f : funcs Σₑ (ar , s)) →
                   VecH Sortsₑ (Carrier ∘ iSortsₑ) ar →
                   Carrier (iSortsₑ s)
if (valN n) ⟨⟩           = λ σ → n
if plus (v₀ ▹ v₁ ▹ ⟨⟩) σ = v₀ σ + v₁ σ
if (varN x) ⟨⟩           = λ σ → σ x

iFuncsₑ : ∀ {ty} → (f : funcs Σₑ ty) → IFuncs Σₑ ty iSortsₑ
iFuncsₑ f = record  { _⟨$⟩_ = if f
                    ; cong = ... }

Semₑ : Algebra Σₑ
Semₑ = iSortsₑ ∥ iFuncsₑ

hSem : Homomorphism ExprAlg Semₑ
hSem = ∣T∣ₕ Semₑ
\end{spec}

De esta forma el valor semántico para la expresión $3 \oplus ``x''$ será:

\begin{spec}
  ′ hSem ′ ExprN ⟨$⟩ e = λ σ → 3
\end{spec}

\noindent donde |e = term plus (term (valN 3) ⟨⟩ ▹ term (varN `` x '') ⟨⟩ ▹ ⟨⟩)|.

\subsubsection*{Semántica del lenguaje target}

En el lenguaje target la semántica para cada expresión es una función parcial que va
de un par consistente de una ``pila'' de naturales y un estado de asignación
de valores a las variables (que llamaremos |Conf|), a otra pila. Esta función es parcial ya que la expresión $add$
puede ejecutarse sólamente si en la pila hay por lo menos dos elementos.
Implementaremos esta parcialidad utilizando el tipo |Maybe|:

\begin{spec}
data Stack : Set where
  ε   : Stack
  _▸_ : ℕ → Stack → Stack

Conf : Set
Conf = Stack × State


iSortsₘ : ISorts Σₘ
iSortsₘ Codeₛ = Conf →-setoid Maybe Stack


ifₘ : ∀ {ar} {s} →  (f : funcs Σₘ (ar , s)) →
                    VecH Sortsₘ (Carrier ∘ iSortsₘ) ar →
                    Carrier (iSortsₘ s)
ifₘ (pushₘ n) ⟨⟩  = λ {(s , σ) → just (n ▸ s)}
ifₘ (loadₘ v) ⟨⟩  = λ {(s , σ) → just (σ v ▸ s)}
ifₘ addₘ ⟨⟩       = λ  {  (n₀ ▸ n₁ ▸ s , σ)  → just (n₀ + n₁ ▸ s) ;
                          (_ , σ)            → nothing
                       }
ifₘ seqₘ (v₀ ▹ v₁ ▹ ⟨⟩) = λ {(s , σ) → v₀ (s , σ) >>= λ s' → v₁ (s' , σ)}


iFuncsₘ : ∀ {ty} → (f : funcs Σₘ ty) → IFuncs Σₘ ty iSortsₘ
iFuncsₘ f = record  { _⟨$⟩_ = ifₘ f
                    ; cong = ... }

Exec : Algebra Σₘ
Exec = iSortsₘ ∥ iFuncsₘ

hexec : Homomorphism CodeAlg Exec
hexec = ∣T∣ₕ Exec
\end{spec}

Como ejemplo consideremos el término

\begin{spec}
c = term seqₘ  (term (pushₘ 3) ⟨⟩ ▹
               (term seqₘ  (term (loadₘ `` x '') ⟨⟩ ▹
                           term add ⟨⟩ ▹
                           ⟨⟩)) ▹
               ⟨⟩)
\end{spec}


\noindent su semántica se obtendrá con el homomorfismo |hexec|:

\begin{spec}
  ′ hexec ′ Codeₛ ⟨$⟩ c = λ {(s , σ) → just (σ " x " + 3 ▸ s)
\end{spec}


\subsection{Traducción}

Tenemos los lenguajes source y target definidos con sus respectivas
semánticas. Podemos graficarlo en el siguiente diagrama:

\begin{diagram}
  |ExprAlg|     &     &   &  &    &|CodeAlg|\\
  \dTo_{|hSem|} &     &   &  &   &\dTo_{|hexec|}\\
  |Semₑ|        &     &   &  &    &|Exec|\\
\end{diagram}


Para poder traducir correctamente un lenguaje a otro según el framework que
presentamos, necesitamos llevar |CodeAlg| y |Exec| a la signatura |Σₑ|. Para ello definimos
una \textbf{traducción}. Como tenemos un sólo sort en cada lenguaje hay una
única opción para definir la traducción de sorts: |ExprN| se traduce
en |Codeₛ|.
La traducción de símbolos de función dará las reglas que se apliquen
cada vez que se deban interpretar los símbolos de |Σₑ| en una |Σₘ|-álgebra.
Estas reglas siguen las ideas para definir el compilador intuitivamente,
como lo mostramos previamente:

\begin{align*}
  comp\;n  &= push\;n\\
  comp\;v  &= load\;v\\
  comp\;e_1 \oplus e_2 &= comp\;e_1 ; comp\;e_2 ; add
\end{align*}


\subsubsection*{Traducción de la signatura}

\begin{spec}
sₑ↝sₘ : sorts Σₑ → sorts Σₘ
sₑ↝sₘ ExprN = Codeₛ

fₑ↝fₘ : ∀ {ar} {s} →  (f : funcs Σₑ (ar , s)) →
                      ΣExpr Σₘ (map sₑ↝sₘ ar) (sₑ↝sₘ s)
fₑ↝fₘ (valN n)  = pushₘ n ∣$∣ ⟨⟩
fₑ↝fₘ plus      = seqₘ ∣$∣  (# (suc zero) ▹
                            (seqₘ ∣$∣ ((# zero) ▹ (addₘ ∣$∣ ⟨⟩) ▹ ⟨⟩)) ▹
                            ⟨⟩)
fₑ↝fₘ (varN v)  = loadₘ v ∣$∣ ⟨⟩

ΣₑtoΣₘ : Σₑ ↝ Σₘ
ΣₑtoΣₘ = record { ↝ₛ = sₑ↝sₘ
                ; ↝f = fₑ↝fₘ
                }
\end{spec}

\subsubsection*{Transformación de las álgebras}

Habiendo definido la traducción |ΣₑtoΣₘ| podemos automáticamente
transformar cualquier |Σₘ|-álgebra en una |Σₑ|-álgebra.
Transformamos entonces |CodeAlg| y |Exec|:

\begin{spec}
CodeAlgₑ : Algebra Σₑ
CodeAlgₑ = ΣₑtoΣₘ 〈 CodeAlg 〉

Execₑ : Algebra Σₑ
Execₑ = ΣₑtoΣₘ 〈 Exec 〉
\end{spec}

\noindent y podemos llevar el homomorfismo |hexec| a la signatura
|Σₑ|:

\begin{spec}
hexecₑ : Homomorphism CodeAlgₑ Execₑ
hexecₑ = ΣₑtoΣₘ 〈 hexec 〉ₕ
\end{spec}

El compilador quedará definido por el único homomorfismo que existe
entre |ExprAlg| y |CodeAlgₑ|, ya que la primera de éstas es inicial:

\begin{spec}
homc : Homomorphism ExprAlg CodeAlgₑ
homc = ∣T∣ₕ CodeAlgₑ
\end{spec}


El diagrama ahora puede verse así:

\begin{diagram}
  |ExprAlg|     &\rTo^{|homc|}  &|CodeAlgₑ|\\
  \dTo_{|hSem|} &             &\dTo_{|hexecₑ|}\\
  |Semₑ|        &              &|Execₑ|\\
\end{diagram}

Para completar el diagrama necesitamos definir un homomorfismo entre
|Semₑ| y |Execₑ| (o al revés). Veremos que para nuestro ejemplo
dar un homomorfismo de |Semₑ| a |Execₑ| ($Enc$ en la terminología
de \cite{janssen-98}) obtiene la corrección del compilador.

Este homomorfismo relaciona las semánticas de cada lenguaje. Puesto que la semántica
del lenguaje source es una función que dado un estado obtiene un natural, en la semántica
del lenguaje target corresponde con poner ese natural en el tope de la pila:

\begin{spec}
Sem→Execₑ : Semₑ ⟿ Execₑ
Sem→Execₑ ExprN =
         record  { _⟨$⟩_  = λ {fₑ (s , σ) → just (fₑ σ ▸ s)}
                 ; cong   =  λ {  {f₀} {f₁} f₀≈f₁ (s , σ) →
                                  cong (λ n → just (n ▸ s)) (f₀≈f₁ σ) }
                 }


condhₛₑₘ : ∀ {ty}  (f : funcs Σₑ ty) →
                   homCond Semₑ Execₑ Sem→Execₑ f
condhₛₑₘ (valN n) ⟨⟩          = λ _ → refl
condhₛₑₘ plus (f₀ ▹ f₁ ▹ ⟨⟩)  = λ _ → refl
condhₛₑₘ (varN v) ⟨⟩          = λ _ → refl

hₛₑₘ : Homomorphism Semₑ Execₑ
hₛₑₘ = record  { ′_′ = Sem→Execₑ
               ; cond = condhₛₑₘ }
\end{spec}

\noindent la prueba de condición de homomorfismo resulta trivial.

Ahora tenemos que el siguiente diagrama conmuta, por inicialidad de |ExprAlg|:

\begin{diagram}
  |ExprAlg|     &\rTo^{|homc|}  &|CodeAlgₑ|\\
  \dTo_{|homSem|} &             &\dTo_{|hexecₑ|}\\
  |Semₑ|        &\rTo^{|hₛₑₘ|}  &|Execₑ|\\
\end{diagram}

\subsection{Extracción de la prueba de corrección}

Veamos cómo podemos obtener la prueba de corrección del compilador
a partir del desarrollo presentado.

El lenguaje de expresiones está definido a partir del álgebra de términos
|ExprAlg|:

\begin{spec}
Expr : Set
Expr = Carrier (ExprAlg ⟦ ExprN ⟧ₛ)
\end{spec}

El resultado de compilar expresiones serán los elementos del álgebra |CodeAlgₑ|:

\begin{spec}
Code : Set
Code = Carrier (CodeAlgₑ ⟦ ExprN ⟧ₛ)
\end{spec}

La función semántica del lenguaje source está definida por el homomorfismo |hSem|, y podemos dar una sintaxis
más sencilla:

\begin{spec}
⟦_⟧_ : Expr → State → ℕ
⟦ e ⟧ σ = (′ hSem ′ ExprN ⟨$⟩ e) σ
\end{spec}

Podemos hacer lo mismo para la semántica del lenguaje target:

\begin{spec}
⟪_⟫ : Code → Conf → Maybe Stack
⟪ c ⟫ = ′ hexecₑ ′ ExprN ⟨$⟩ c
\end{spec}


El compilador está definido por el homomorfismo |homc|:

\begin{spec}
compₑ : Expr → Code
compₑ e = ′ homc ′ ExprN ⟨$⟩ e 
\end{spec}

La prueba de corrección del compilador expresa que si compilamos una expresión y
ejecutamos el código resultante a partir de la pila |s| y un estado |σ|, el
resultado será la pila |s| con el valor semántico de la expresión agregado en el tope:


\begin{spec}
correct : ∀  (e : Expr) → (s : Stack) → (σ : State) → 
             ⟪ compₑ e ⟫ (s , σ) ≡ just ((⟦ e ⟧ σ) ▸ s)
\end{spec}

A partir del framework algebraico se puede extraer esta prueba:

\begin{spec}
correct e s σ = (elim≈ₕ unic ExprN e e refl) (s , σ)
  where  unic : (hexecₑ ∘ₕ homc) ≈ₕ (hₛₑₘ ∘ₕ homSem)
         unic = unique (∣T∣init Σₑ) Execₑ (hexecₑ ∘ₕ homc) (hₛₑₘ ∘ₕ homSem)
\end{spec}

El desarrollo completo del ejemplo puede verse en |Ejemplos/CorrectC.agda|, en \cite{univAlgebra}.

\bibliographystyle{apalike}
\begin{flushleft}
\bibliography{biblio}
\end{flushleft}



\end{document}
