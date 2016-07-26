\documentclass[a4paper,twoside,12pt]{article}
\usepackage{amsmath}
\usepackage{mathpartir}
\usepackage[small,nohug,heads=vee]{diagrams}
\diagramstyle[labelstyle=\scriptstyle]

%include agda.fmt
%include unicode.fmt

\begin{document}

\title{Formalización de Álgebras Universales en Agda y su utilización
       para la traducción correcta de lenguajes}

\author{Emmanuel Gunther}
       
\maketitle

\begin{abstract}

En el presente trabajo presentamos una formalización en el lenguaje
Agda \cite{agda} de Álgebras Universales Heterogéneas, definiendo
los conceptos de signatura, álgebras, homomorfismo, inicialidad y ál-
gebra de términos. Con estos conceptos formalizamos un framework
para traducción de lenguajes de acuerdo al esquema que presenta Jansen
\cite{jansen-98} y lo utilizamos para construir un compilador sencillo
probando su corrección.

\end{abstract}

\section{Introduction}

Una manera de pensar la sintaxis y semántica de los lenguajes es mediante
Álgebras Universales. La sintaxis de un lenguaje es el álgebra de términos $T$
de una signatura $\Sigma$ y un álgebra $A$ de $\Sigma$ es un dominio
semántico. La función semántica es el único homomorfismo que existe entre
$T$ y $A$, que está dado por inicialidad del álgebra de términos.

Varios trabajos han explorado el enfoque algebraico para dar un framework
general para la traducción de lenguajes de manera correcta, y en particular
para la construcción de compiladores correctos. En \cite{jansen-98} se analizan
diversos enfoques y se propone un marco general para la traducción de lenguajes.

En este trabajo formalizamos un enfoque similar al que se propone en \cite{jansen-98}.
Se puede resumir con el siguiente diagrama:

DIAGRAMA
%% \begin{diagram}

%% \end{diagram}

$T_s$ y $T_t$ son el álgebra de términos de dos signaturas $\Sigma_s$ y $\Sigma_t$
respectivamente, y se corresponden con la sintaxis abstracta de los lenguajes fuente y
target. La semántica de ambos lenguajes está definida mediante las álgebras $Sem_s$ y
$Sem_t$, y los homomorfismos $hSem_s$ y $hSem_t$ dados por inicialidad. Un
\textit{transformador de álgebras} $\delta$ permite llevar las álgebras $T_t$ y $Sem_t$
a la signatura $\Sigma_s$ y el traductor $Tr$ es el homomorfismo dado por inicialidad
de $T_s$. Por último un homomorfismo $Dec$ entre $\delta(Sem_t)$ y $Sem_s$ hace conmutar
al diagrama obteniendo la corrección del traductor.

El concepto de \textit{transformador de álgebras} lo definiremos formalmente y se
corresponde con lo que se denomina \textit{polynomial derivor} en \cite{jansen-98},
o \textit{interpretación} en alguna literatura sobre álgebra universal (buscar referencia).

En la primera sección de este artículo formalizamos los conceptos de signatura, álgebra,
homomorfismo, inicialidad y álgebra de términos, obteniendo
una librería en Agda para el uso de álgebras universales en general. Se discuten
algunas decisiones de implementación. El resultado es similar al que obtiene
Venanzio Capretta en \cite{capretta-99}, con su formalización de álgebras universales en
Coq (\cite{coq}), utilizando setoides para los carrier de las álgebras; sin
embargo presenta algunas diferencias de implementación, como el uso de vectores heterogéneos.

En la segunda sección formalizamos el concepto de transformación de álge-
bras, para llevar un álgebra de una signatura $\Sigma_1$ en una de la signatura
$\Sigma_0$, y probamos que los homomorfismos se preservan.

En la tercera sección damos un ejemplo de un compilador de un lenguaje
de expresiones aritméticas y booleanas simple, en un lenguaje que manipula
una pila, y mostramos su corrección mediante el framework de traducción con
álgebras universales.

\section{Álgebras Universales}

\subsection{Signatura, álgebra y homomorfismo}

Presentamos una formalización de Álgebra Universal en Agda.
Se asume familiaridad con algún lenguaje con tipos dependientes de parte del lector. Para
evitar complicaciones técnicas del lenguaje Agda en particular obviamos algunos
detalles en las definiciones, facilitando su lectura. Por ejemplo algunos parámetros
implícitos no son detallados en este texto. La librería completa de álgebras
universales puede verse en UniversalAlgebra.agda (referencia al archivo cuando
esté publicado).

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

De acuerdo al \textit{Handbook of Logic in Computer Science} (\cite{handbook}), una
\textbf{signatura} es un par $(S,F)$ de conjuntos, el primero llamado \textit{sorts} y el segundo
\textit{operaciones} (también llamados \textit{símbolos de función}). Una operación es una 3-upla
$(w:[s_1,...,s_n] \rightarrow s)$ consistente de un nombre, una lista de sorts y un sort.

Llamaremos \textit{aridad} a la lista de sorts $[s_1,...,s_n]$, \textit{target sort} al sort $s$ y
$tipo$ al par $([s_1,...,s_n],s)$ \footnote{En la bibliografía sobre álgebras heterogéneas varía
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

  ΣType : Set
  ΣType = List sorts × sorts
  
open Signature

\end{code}

Una ventaja de tener definido de esta forma la signatura es que el mismo sis-
tema de tipos de Agda nos permite definir propiedades sólo para las operaciones
de determinada aridad, por ejemplo podríamos definir:

\begin{spec}
  p : ∀ {Σ : Signature} {ty : ΣType Σ} → funcs Σ ty → P
\end{spec}

\noindent una propiedad que sólo está definida para las operaciones con tipo |ty|
En una implementación donde se define a las operaciones como una lista de tipos
(como en \cite{capretta-99}) sería bastante más complicado definir una propiedad
restringiendo el tipo de la operación. Notemos también que con esta definición
podríamos tener una signatura con ningún sort (el Set vacío) o también una con
una cantidad infinita de sorts.

Veamos un ejemplo de una signatura con dos sorts refiriendo a valores
booleanos y naturales, con sus operaciones:

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
Σ₁ = record { sorts = S
            ; funcs = F
            }
\end{code}

\subsection*{Álgebra}

Dada una signatura $\Sigma$, un \textbf{álgebra} $A$ de $\Sigma$ (o una $\Sigma$-álgebra)
consta de una familia de conjuntos indexada en los sorts de $\Sigma$ llamado los
\textit{carriers} (o \textit{interpretación de sorts}) de $A$ (llamaremos $A_s$ al carrier del sort $s$), y para cada operación
$w$ con tipo $[s_1,...,s_n],s$ una función total $w_A : A_{s_1} \times ... \times A_{s_n} \rightarrow A_s$.
Llamaremos \textit{interpretación} de $w$ a esta función.

Para implementar los carriers de las álgebras utilizamos setoides.
En teoría de tipos, un setoide es un tipo que tiene definido una relación de equivalencia:

\begin{spec}
record Setoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    isEquivalence : IsEquivalence _≈_
\end{spec}

El |Carrier| del setoide es el tipo de los elementos que lo componen y |_≈_|
una relación binaria sobre el carrier. También se requiere la prueba de que esta
relación es de equivalencia.
Dados dos setoides $S_1$ y $S_2$ se define el tipo $S_1 \longrightarrow S_2$, que
consiste de la función que va del carrier de $S_1$ al carrier de $S_2$ (cuya notación
en Agda será con el símbolo |_⟨$⟩_|) y una prueba de que conserva la relación de igualdad,
es decir, si $s_1$ |≈|$_{S_1}$ $s_1'$ entonces $f \, s_1$ |≈|$_{S_2}$ $f \, s_1'$
(|cong|, en Agda).

Una diferencia importante entre usar setoides en lugar de |Sets| es que podemos tener
carriers de álgebras con una noción de igualdad que no sea simplemente la igualdad
proposicional. En particular si quisiéramos definir como
carrier un tipo funcional, no podríamos tener la igualdad extensional que uno
esperaría, ya que no puede probarse en Agda (explicar mejor esto).
Con setoides se puede definir la relación extensional y probar que es de equivalencia.
También fácilmente se podrían definir álgebras cocientes.

Para definir los carriers de una $\Sigma$-álgebra entonces usaremos setoides:

\begin{code}
ISorts : ∀ {ℓ₁ ℓ₂} → (Σ : Signature) → Set _
ISorts {ℓ₁} {ℓ₂} Σ = (sorts Σ) → Setoid ℓ₁ ℓ₂
\end{code}

En una $\Sigma$-álgebra $A$ entonces, para un sort $s$ de $\Sigma$, su interpretación
será un setoide. Para definir la interpretación de una operación utilizaremos
\textit{vectores heterogéneos}.

Dado un tipo $T$ indexado en $I$, y una lista de índices $[i_1,...,i_n]$,
un vector heterogéneo es una colección de $n$ elementos, donde cada uno es de
tipo $T\,i$:

\begin{spec}
data VecH (I : Set) (A : I -> Set _) : List I → Set _ where
  ⟨⟩  : VecH I A []
  _▹_ : ∀ {i} {is} → (v : A i) → (vs : VecH I A is) → VecH I A (i ∷ is)
\end{spec}

Dada una familia de relaciones $R$ indexada en un tipo $I$, podemos definir la
relación de dos vectores extendiendo $R$. Nos referiremos a esta extensión con
el símbolo |~v|. Si la relación es la correspondiente a la de un setoide para
cada elemento |i : I| de una lista |is|, podemos definir el setoide de los
vectores heterogéneos:

\begin{spec}
VecSet :  ∀ {ℓ₁ ℓ₂} → (I : Set) → (A : I → Setoid ℓ₁ ℓ₂) →
          List I → Setoid _ _
VecSet = ...
\end{spec}

El carrier de este setoide es el tipo de los vectores con índices en |I|, lista de índices
|is| y elementos en |Carrier (A i)|, donde cada |i| es un elemento de |is|.
La relación de equivalencia es la extensión a vectores de la familia de relaciones |_≈_ ∘ A|.

En |VecH.agda| está implementada la librería de vectores heterogéneos con estas definiciones
y más propiedades del tipo.

Podemos entonces definir la interpretación de las operaciones. Dada una operación $f$ con tipo
$ty$, y dada una interpretación de sorts $is$, la intepretación de $f$ se define como una función
entre el setoide de los vectores heterogéneos con los sorts de $\Sigma$ como índices, $is$ como
la familia indexada en los sorts de $\Sigma$ y la aridad de $f$ como lista de índices de cada
elemento:

\begin{code}
IFuncs :  ∀ {ℓ₁ ℓ₂} → (Σ : Signature) → (ty : ΣType Σ) →
          ISorts {ℓ₁} {ℓ₂} Σ → Set _
IFuncs Σ (ar , s) is = VecSet (sorts Σ) is ar ⟶ is s
\end{code}

Finalmente definimos el tipo de las $\Sigma$-álgebras:

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

\begin{code}
_⟿_ : ∀  {Σ : Signature} {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} →
         (A : Algebra {ℓ₁} {ℓ₂} Σ) → (A' : Algebra {ℓ₃} {ℓ₄} Σ) →
         Set _
_⟿_ {Σ} A A' = (s : sorts Σ) → A ⟦ s ⟧ₛ ⟶ A' ⟦ s ⟧ₛ
\end{code}

Procedamos ahora a definir la condición de homomorfismo. Tenemos varias
cosas que intervienen en la ecuación (1). Primero, dado un símbolo
de función $f$ con aridad $[s_1,...,s_n]$, la interpretación $f$ en una
$\Sigma$-álgebra $A$ toma como argumento vectores heterogéneos donde cada
elemento $a_i$ pertenece a la interpretación de $s_i$ en $A$. Definamos
el tipo de estos vectores para facilitar la notación. Sea |A| una $\Sigma$-álgebra
y |ar| una aridad de $\Sigma$:

\begin{spec}
idom : _
idom {Σ} ar A = VecH (sorts Σ) (Carrier ∘ _⟦_⟧ₛ A) ar
\end{spec}

En la parte derecha de la ecuación (1) tenemos la aplicación de la función $h$ en
cada elemento de $(a_1,...,a_n)$. Definimos esta notación en Agda, correspondiente
a ``mapear'' una función entre álgebras |h| a un vector en |idom ar A| (donde |ar|
es una aridad y |A| un álgebra), llamaremos a esta función |map⟿| (no daremos los
detalles).

Podemos entonces formalizar la condición de homomorfismo |homCond|: Si
|h : A ⟿ A'| y |f : funcs Σ (ar , s)|, para todo |as : idom ar A|, debe darse
la igualdad en el setoide correspondiente a la interpretación de |s| en |A'|, entre
la aplicación de |h| al resultado de aplicar la interpretación de |f| en |A| al vector
|as| y la aplicación de la interpretación de |f| en |A'| al resultado de mapear
|h| a |as|:

\begin{spec}
homCond A A' h f = (as : idom ar A) →  _≈_ (A' ⟦ s ⟧ₛ)
                                       (h s ⟨$⟩ (A ⟦ f ⟧ ⟨$⟩ as))
                                       (A' ⟦ f ⟧ ⟨$⟩ (map⟿ h as))
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
otro elemento $e' \in A$ se da que $e = e'$. Podemos definir esta noción en
Agda generalizando la noción de igualdad:

\begin{spec}
Unicity : ∀ {ℓ₁} {ℓ₂} → (A : Set ℓ₁) → Rel A ℓ₂ → Set _ 
Unicity A _≈_ = Σ[ a ∈ A ] ((a' : A) → a ≈ a')
\end{spec}

Dado un tipo |A|, y una relación binaria |_≈_| entre elementos de |A|,
un |a : A| es único con respecto a |_≈_| si para todo otro elemento |a' : A|,
|a| y |a'| están relacionados.

Ahora deberíamos decir cuándo dos homomorfismos son iguales. La igualdad
que consideramos será la extensional: Dos funciones $f$ y $g$ son iguales si,
dados dos elementos $a$ y $b$ tales que $a = b$, entonces $f\,a = g\,b$.

Definamos la igualdad extensional en Agda, generalizando las relaciones de igualdad:

\begin{spec}
ExtProp : _
ExtProp _≈A_ _≈B_ f g = (a a' : A) → a ≈A a' → f a ≈B g a'
\end{spec}

La igualdad entre dos homomorfismos |H| y |H'| será un tipo con un único
constructor conteniendo la propiedad extensional para cada sort de la signatura:

\begin{spec}
data _≈ₕ_  {Σ} {A : Algebra Σ} {A' : Algebra Σ}
           (H H' : Homomorphism A A') : Set _ where
  ext :  ((s : sorts Σ) → ExtProp  (_≈_ (A ⟦ s ⟧ₛ)) (_≈_ (A' ⟦ s ⟧ₛ))
                                   (_⟨$⟩_ (′ H ′ s)) (_⟨$⟩_ (′ H' ′ s))) →
         H ≈ₕ H'
\end{spec}

Finalmente podemos definir cuándo un álgebra es inicial:

\begin{spec}
record Initial (Σ : Signature) : Set _ where
  field
    alg      : Algebra Σ
    init     : (A : Algebra Σ) → Unicity (Homomorphism alg A) (_≈ₕ_)
\end{spec}

Un álgebra inicial de una signatura $\Sigma$ consta de una $\Sigma$-álgebra
|alg| y la prueba de que la misma es inicial, es decir, que para toda otra álgebra
|A|, hay un homomorfismo entre |alg| y |A| y es único.

\subsection*{Álgebra de términos}

A partir de una signatura $\Sigma$ puede construirse un \textbf{álgebra de términos},
donde los elementos que conforman los carriers son los términos generados por los
símbolos de función de $\Sigma$. Estos carriers son llamados el \textit{Herbrand Universe}
de $\Sigma$. Como ejemplo, consideremos la signatura $\Sigma_1$, definida anteriormente,
la cual contenía dos sorts |bool| y |nat|. El carrier del álgebra de términos de $\Sigma_1$ para
el sort |nat| contiene a los elementos |fzero|, |fsuc fzero|, |fusc (fsuc fzero)|, etc.

Procedamos a definir el \textit{Herbrand Universe} de una signatura $\Sigma$ como un tipo indexado
en los sorts de $\Sigma$. Un elemento de este tipo será un término, que consta de un símbolo
de función y un vector heterogéneo donde cada elemento será un |HU| indexado en el sort correspondiente
a la aridad de la función:

\begin{spec}
data HU (Σ : Signature) : (s : sorts Σ) → Set where
  term : ∀ {ar} {s} →  (f : funcs Σ (ar , s)) →
                       (ts : VecH (sorts Σ) (HU Σ) ar) → HU Σ s
\end{spec}

El álgebra de términos de $\Sigma$ tendrá como carrier de un sort $s$ al Herbrand Universe
indexado en $s$. La igualdad de los elementos del carrier será la igualdad proposicional
(dos elementos son iguales sólo si lo son sintácticamente). La interpretación de un símbolo
de función |f| aplicado a un vector |vs| será el término |term f vs|:

\begin{spec}
∣T∣ : (Σ : Signature) → Algebra Σ
∣T∣ Σ = record  { _⟦_⟧ₛ = PE.setoid ∘ HU Σ
                ; _⟦_⟧  = λ f → termFuns f
                }
  where termFuns f = record  { _⟨$⟩_ = term f
                             ; cong = ...
                             }
\end{spec}

La función setoid definida en la librería estándar de Agda construye un setoide
a partir de un tipo, donde la igualdad es la proposicional.

Podemos ahora probar que el álgebra de términos de una signatura $\Sigma$ es inicial,
es decir, que para cualquier $\Sigma$-álgebra $A$ existe un homomorfismo y es único.

El homomorfismo entre |∣T∣ Σ| y |A| puede definirse recursivamente. Tenemos que definir
una función |h| que lleve un término |term f ts| a la interpretación de |f| en |A| aplicado
al vector resultante de mapear |h| en |ts|. Quisiéramos definir exactamente esto en
Agda así:

\begin{spec}
∣T∣→A : ∀ {A : Algebra Σ} (s : sorts Σ) → HU Σ s → Carrier (A ⟦ s ⟧ₛ)
∣T∣→A {A = A} s (term f ts) = A ⟦ f ⟧ ⟨$⟩ (mapV ∣T∣→A ts)
\end{spec}

\noindent sin embargo el chequeador de terminación de Agda no puede asegurar la terminación.
Lo resolvemos con dos funciones mutuamente recursivas donde vamos aplicando ∣T∣→A en cada
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

Con esta definición el chequeador de terminación de Agda no se queja. Podemos
igual probar que aplicar |map∣T∣→A| a un vector es igual a mapear |∣T∣→A| en
ese vector, de manera trivial:

\begin{spec}
map∣T∣→A≡mapV : ∀ {Σ}  {A : Algebra Σ} {ar : Arity Σ}
                       {ts : VecH (sorts Σ) (HU Σ) ar} →
                       map∣T∣→A ts ≡ mapV ∣T∣→A ts
map∣T∣→A≡mapV {ar = []} {⟨⟩} = PE.refl
map∣T∣→A≡mapV {A = A} {s₀ ∷ ar} {t₀ ▹ ts} =
                  cong (λ ts' → ∣T∣→A s₀ t₀ ▹ ts') map∣T∣→A≡mapV
\end{spec}

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
$\theta(T_t)$, $\theta(Sem_t)$ y $\theta(hSem_t)$) y si damos un homomorfismo $h$ entre $Sem_s$
y $\theta(Sem_t)$, el traductor quedará definido por el único homomorfismo que hay entre $T_s$ y
$\theta(T_t)$, y su corrección por la conmutación del diagrama resultante, gracias a la inicialidad
de $T_s$:

\begin{diagram}
  T_s     &\rTo^{trad}  &\theta(T_t)\\
  \dTo_{hSem_s} &          &\dTo_{\theta(hSem_t)}\\
  Sem_s        &\rTo^{h}  &\theta(Sem_t)\\
\end{diagram}

Podemos definir cada álgebra transformada, interpretando los sorts y los símbolos de función
en los carriers correspondientes. Sin embargo este trabajo sería repetitivo y deberíamos hacerlo
para cada álgebra de la signatura $\Sigma_t$ que querramos transformar. También deberíamos redefinir
los homomorfismos, probando que se preserva la condición al cambiar de signatura.

En lugar de hacer eso, definiremos un (meta)lenguaje para traducir cualquier álgebra de una signatura en otra.

\subsection*{Traducción de signaturas}

Dadas dos signaturas $\Sigma_s$ y $\Sigma_t$, para llevar álgebras de $\Sigma_t$ en $\Sigma_s$, definimos
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

Y ahora damos la traducción de los símbolos de función:

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
y |t↝ : Σₛ ↝ Σₜ|. A partir de una |Σₜ|-álgebra |A| podemos definir una
|Σₛ|-álgebra de la siguiente manera:

\begin{itemize}
  \item Interpretamos a cada sort |sˢᵢ| con |a ⟦ ↝ₛ t↝ sˢᵢ ⟧|.
  \item Para cada símbolo de función |fˢᵢ| con aridad |arᵢ|, definimos la interpretación de la siguiente manera:
    \begin{itemize}
    \item Si |↝f t↝ fˢᵢ| es |# h|, con |h : Fin (length arᵢ)| definiremos la interpretación
          \begin{spec}
            ifˢᵢ vs = vs ‼ h
          \end{spec}
    \item Si |↝f t↝ fˢᵢ| es |g ∣$∣ ⟨ e₁ , ... , eₚ ⟩ |, donde |g : funcs Σₜ ar' s'| y |e₁ , ... , eₚ| son
          |ΣExpr|:
          \begin{spec}
            ifˢᵢ vs = A ⟦ g ⟧ ⟨$⟩ ies
          \end{spec}

          donde |ivs| es el vector resultante de interpretar cada expresión |e₁,...,eₚ|, y posiblemente
          ocurran elementos de |vs|.
    \end{itemize}
\end{itemize}

Con estas ideas intuitivas podemos definir formalmente la transformación de álgebras. No mostraremos
los detalles, pueden encontrarse en (CITA).

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
naturales y un estado de asignación de valores a las variables.
$push\,n$ pone en el tope de la pila el valor $n$; $load\,v$ pone en el tope de la pila el valor
de la variable $v$ en el estado; $c_1 ; c_2$ ejecuta $c_1$ y luego $c_2$ a partir del stack resultante;
y por último $add$ a partir de una pila que tiene al menos dos elementos en el tope, los quita de la pila
y pone la el resultado de sumarlos.

Podemos definir la sintaxis de ambos lenguajes a partir de dos signaturas |Σₑ| y |Σₘ|,
obteniendo las respectivas álgebras de términos:

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

Las semánticas de ambos lenguajes las definimos a partir de álgebras
de las signaturas, obteniendo un homomorfismo desde el álgebra de términos:

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

\begin{spec}
data Stack : Set where
  ε   : Stack
  _▸_ : ℕ → Stack → Stack

Conf : Set
Conf = Stack × State


iSortsₘ : ISorts Σₘ
iSortsₘ Codeₛ = Conf →-setoid Maybe Conf


ifₘ : ∀ {ar} {s} →  (f : funcs Σₘ (ar , s)) →
                    VecH Sortsₘ (Carrier ∘ iSortsₘ) ar →
                    Carrier (iSortsₘ s)
ifₘ (pushₘ n) ⟨⟩  = λ {(s , σ) → just (n ▸ s , σ) }
ifₘ (loadₘ v) ⟨⟩  = λ {(s , σ) → just (σ v ▸ s , σ)}
ifₘ addₘ ⟨⟩       = λ {  (n₀ ▸ n₁ ▸ s , σ) → just ((n₀ + n₁ ▸ s) , σ) ;
                         (_ , σ) → nothing
               }
ifₘ seqₘ (v₀ ▹ v₁ ▹ ⟨⟩) = λ sσ → v₀ sσ >>= v₁


iFuncsₘ : ∀ {ty} → (f : funcs Σₘ ty) → IFuncs Σₘ ty iSortsₘ
iFuncsₘ f = record  { _⟨$⟩_ = ifₘ f
                    ; cong = ... }

Exec : Algebra Σₘ
Exec = iSortsₘ ∥ iFuncsₘ

hexec : Homomorphism CodeAlg Exec
hexec = ∣T∣ₕ Exec
\end{spec}


Tenemos entonces el siguiente diagrama:

\begin{diagram}
  |ExprAlg|     &     &   &  &    &|CodeAlg|\\
  \dTo_{|hSem|} &     &   &  &   &\dTo_{|hexec|}\\
  |Semₑ|        &     &   &  &    &|Exec|\\
\end{diagram}


Para poder traducir un lenguaje a otro, necesitamos llevar
|CodeAlg| y |Exec| a la signatura |Σₑ|. Para ello definimos
una transformación.

\begin{spec}
sₑ↝sₘ : sorts Σₑ → sorts Σₘ
sₑ↝sₘ ExprN = Codeₛ

fₑ↝fₘ : ∀ {ar} {s} → (f : funcs Σₑ (ar , s)) →
                      ΣExpr Σₘ (map sₑ↝sₘ ar) (sₑ↝sₘ s)
fₑ↝fₘ (valN n) = pushₘ n ∣$∣ ⟨⟩
fₑ↝fₘ plus     = seqₘ ∣$∣ (# (suc zero) ▹ (seqₘ ∣$∣ ((# zero) ▹ (addₘ ∣$∣ ⟨⟩) ▹ ⟨⟩)) ▹ ⟨⟩)
fₑ↝fₘ (varN v) = loadₘ v ∣$∣ ⟨⟩

ΣₑtoΣₘ : Σₑ ↝ Σₘ
ΣₑtoΣₘ = record { ↝ₛ = sₑ↝sₘ
                ; ↝f = fₑ↝fₘ
                }
\end{spec}
(explicar un poco más la transformación, con un ejemplo informal antes)

Podemos entonces llevar las álgebras |CodeAlg| y |Exec| a |Σₑ|:

\begin{spec}
CodeAlgₑ : Algebra Σₑ
CodeAlgₑ = ΣₑtoΣₘ 〈 CodeAlg 〉

Execₑ : Algebra Σₑ
Execₑ = ΣₑtoΣₘ 〈 Exec 〉
\end{spec}

Tenemos por inicialidad un homomorfismo entre |ExprAlg| y
|CodeAlgₑ|:

\begin{spec}
homc : Homomorphism ExprAlg CodeAlgₑ
homc = ∣T∣ₕ CodeAlgₑ
\end{spec}

\noindent y podemos llevar el homomorfismo |hexec| a la signatura
|Σₑ|:

\begin{spec}
hexecₑ : Homomorphism CodeAlgₑ Execₑ
hexecₑ = ΣₑtoΣₘ 〈 hexec 〉ₕ
\end{spec}

El diagrama ahora puede verse así:

\begin{diagram}
  |ExprAlg|     &\rTo^{|homc|}  &|CodeAlgₑ|\\
  \dTo_{|hSem|} &             &\dTo_{|hexecₑ|}\\
  |Semₑ|        &              &|Execₑ|\\
\end{diagram}

Para completar el diagrama necesitamos definir un homomorfismo entre
|Semₑ| y |Execₑ| (Jansen dice que debería ser al revés, pero es bastante
más complicado. VER ESTO):

\begin{spec}
Sem→Execₑ : Semₑ ⟿ Execₑ
Sem→Execₑ ExprN =
         record  { _⟨$⟩_ = λ {fₑ (s , σ) → just (fₑ σ ▸ s , σ)}
                 ; cong =  λ { {f₀} {f₁} f₀≈f₁ (s , σ) →
                           cong (λ n → just (n ▸ s , σ)) (f₀≈f₁ σ) }
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

Con este homomorfismo tenemos que el siguiente diagrama conmuta:

\begin{diagram}
  |ExprAlg|     &\rTo^{|homc|}  &|CodeAlgₑ|\\
  \dTo_{|homSem|} &             &\dTo_{|hexecₑ|}\\
  |Semₑ|        &\rTo^{|hₛₑₘ|}  &|Execₑ|\\
\end{diagram}

Veamos entonces cómo podemos obtener la prueba de corrección del compilador
a partir del enfoque algebraico.

El lenguaje de expresiones está definido a partir del álgebra de términos
|ExprAlg|:

\begin{spec}
Expr : Set
Expr = Carrier (ExprAlg ⟦ ExprN ⟧ₛ)
\end{spec}

La función semántica está definida por el homomorfismo |hSem|, y podemos dar una sintaxis
más sencilla:

\begin{spec}
⟦_⟧_ : Expr → State → ℕ
⟦ e ⟧ σ = (′ hSem ′ ExprN ⟨$⟩ e) σ
\end{spec}

El resultado de compilar expresiones serán los elementos del álgebra |CodeAlgₑ|:

\begin{spec}
Code : Set
Code = Carrier (CodeAlgₑ ⟦ ExprN ⟧ₛ)
\end{spec}

Podemos extraer el compilador a partir del homomofirmos |homc|:

\begin{spec}
compₑ : Expr → Code
compₑ e = ′ homc ′ ExprN ⟨$⟩ e 
\end{spec}

Finalmente, la corrección del compilador se extrae del desarrollo presentado:

\begin{spec}
correct : ∀  (e : Expr) → (σ : State) → 
             ⟪ compₑ e ⟫ (ε , σ) ≡ just ((⟦ e ⟧ σ) ▸ ε , σ)
correct e σ = (elim≈ₕ unic ExprN e e refl) (ε , σ)
  where  unic : (hexecₑ ∘ₕ homc) ≈ₕ (hₛₑₘ ∘ₕ homSem)
         unic = unique (∣T∣init Σₑ) Execₑ  (hexecₑ ∘ₕ homc)
                                           (hₛₑₘ ∘ₕ homSem)
\end{spec}

\bibliographystyle{abbrvnat}
\begin{flushleft}
\bibliography{biblio}
\end{flushleft}


\end{document}
