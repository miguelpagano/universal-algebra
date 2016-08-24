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

%include ejemplo2.lagda

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
_⟦_⟧ₛ* : ∀ {Σ} {ℓ₁} {ℓ₂}  → (A : Algebra {ℓ₁} {ℓ₂} Σ)
                          → (ar : Arity Σ) → Set _
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
la aplicación de la función $h$ en cada elemento de $(a_1,...,a_n)$. Definimos esta noción en Agda. Si
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
      |t₁ : HU Σ s₁| , ... ,|tₙ : HU Σ sₙ|, entonces |term f ts : HU Σ s|.
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
de la función de interpretación por cuestiones de simplicidad.

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

Finalmente sólo resta mostrar que este homomorfismo es único con respecto a la igualdad
|_≈ₕ_|, salvo equivalencias. Es decir, debemos probar que dados dos homomorfismos |h₁| y |h₂|
entre |∣T∣ Σ| y |A|, para todo elemento |term f ts : HU Σ s| se da:

\begin{spec}
    ′ h₁ ′ s ⟨$⟩ term f ts
    ≈ₛ
    ′ h₂ ′ s ⟨$⟩ term f ts
\end{spec}

\noindent donde |≈ₛ| es la relación de igualdad del carrier del sort |s| en el álgebra |A|,
es decir |_≈_ A ⟦ s ⟧ₛ|.

Podemos dar la prueba en Agda así:

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
                  where  mapV≡ :  (ar : Arity Σ) → (ts₀ : VecH (sorts Σ) (HU Σ) ar) →
                                 (mapV (_⟨$⟩_ ∘ ′ h₁ ′) ts₀) ∼v
                                 (mapV (_⟨$⟩_ ∘ ′ h₂ ′) ts₀)
                         mapV≡ = ...
\end{spec}

\noindent mapV≡ es la extensión de la prueba |uni| a vectores, y es mutuamente recursiva con ésta.
No damos su definición por cuestiones de simplicidad.

