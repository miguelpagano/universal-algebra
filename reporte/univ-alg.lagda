\section{Universal Algebra}

We present a formalisation of some concepts of Universal Algebra, included the proof
of initiality of the term algebra, in Agda.

\paragraph{Agda}
Agda is a functional programming language with dependent types, based on the
Martin Löf's intuitionistic type theory...

We show the main definitions of the development, ommiting some technical details.
The full code is available to download on \url{https://git.cs.famaf.unc.edu.ar/semantica-de-la-programacion/algebras-universales/UnivAlgebra.agda}.

All the definitions that we present in this section are based on the \textit{Handbook of Logic in Computer Science}, (\cite{handbook}).

\subsection{Signature, algebra and homomorphism}

\subsection*{Signature}

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

A \textbf{signature} is a pair $(S,F)$ of sets, called \textit{sorts} and \textit{operations} (or \textit{function symbols}) respectively. An operation is a 3-uple $(w,[s_1,...,s_n],s)$ that consists of a \textit{name}, a list of sorts, and another sort, usually writed $(w : [s_1,...,s_n] \rightarrow s)$. The list of sorts $[s_1,...,s_n]$ is called \textit{arity}, the sort $s$ is called the \textit{target sort} and \textit{type} is the pair $([s_1,...,s_n],s)$. \footnote{In the bibliography of heterogeneous universal algebras the notion of arity may change. In the handbook is called \textit{arity} to what we call \textit{type}.}

We define signature in Agda, with a record with two fields. |sorts| is a Set and
|funcs| is a family of sets indexed in the types of operations:

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

An adventage of defining signature of this way is that the type system of Agda
allows to define properties of operations of a given arity. I.e., we can define a type
in Agda referring to the operations of a particular arity or type. This approach is
more type-theoretic than defining the operations with a list of arities, like in
\cite{capretta-99}, and we'll see some important adventages when we define the
translation of signatures.

We show two examples of signatures. The second one shows the posibility of define
a signature with infinite operations.

\paragraph{Example 1} A language with natural and boolean expressions.

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

\paragraph{Ejemplo 2} The language of arithmetic expressions that we present at introduction.

%include ejemplo2.lagda

\noindent Note that we have infinite function symbols, one for each natural number (constructor |valN|), and
one for each variable (contructor |varN|).

\subsection*{Algebra}

Let $\Sigma$ be a signature, an \textbf{algebra} $\mathcal{A}$ of $\Sigma$, or a $\Sigma$-algebra, consists
of a family of sets indexed on the sorts of $\Sigma$, called the \textit{carriers} (or \textit{sorts interpretation})
of $\mathcal{A}$ (we call $\mathcal{A}_s$ the carrier of the sort $S$ in $\mathcal{A}$), and for each operation
$w$ with type $[s_1,...,s_n],s$ a total function $w_A : \mathcal{A}_{s_1} \times ... \times \mathcal{A}_{s_n} \rightarrow \mathcal{A}_s$.
We call \textit{interpretation} of $w$ to this function.

We proceed to define the interpretation of sorts. Let's considere the algebra corresponding
to the semantics of the expressions language that we introduced previoulsy. For each expression, the semantics
is a function from states to natural numbers. Thus, each element of the interpretation of the sort of
the expressions will be a function, and we have an issue to define equality of this elements in Agda. Two
functions extensionally equal (i.e., pointwise equality) are not propositionally equals in Agda, so if we
implement the carrier of sorts with Sets we lose the equality of functions.

We use \textbf{setoids}, so we can represent a set with an arbitrary equivalence relation.

\paragraph{Setoids} blabla


Let's define the interpretation of sorts (or carriers):

\begin{code}
ISorts : ∀ {ℓ₁ ℓ₂} → (Σ : Signature) → Set _
ISorts {ℓ₁} {ℓ₂} Σ = (sorts Σ) → Setoid ℓ₁ ℓ₂
\end{code}

\noindent An element in |ISorts Σ s| is a setoid, and it represents the interpretation of sort
|s| in a |Σ|-algebra.

In order to define the interpretation of a function symbol $f$, with type $[s_1,...,s_n] \rightarrow s$,
in a $\Sigma$-algebra $\mathcal{A}$, we have to define a total function with domain
$\mathcal{A}_{s_1} \times ... \times \mathcal{A}_{s_n}$ and codomain $\mathcal{A}_{s}$. We use
\textit{vectors} to implement the domain of function interpretations, but this vectors will
contain element of different types, according to the arity. We define the type of
\textit{heterogeneous vectors}.

\paragraph{Heterogeneous vectors} blablabla

Let's define the interpretation of operations. Let $f$ be an operation with type $ty$,
and let $is$ be the interpretation of sorts; the interpretation of $f$ is a function
from the setoid of heterogeneous vectors to the interpretation of the target sort of
$f$:

\begin{code}
IFuncs :  ∀ {ℓ₁ ℓ₂} → (Σ : Signature) → (ty : ΣType Σ) →
          ISorts {ℓ₁} {ℓ₂} Σ → Set _
IFuncs Σ (ar , s) is = VecSet (sorts Σ) is ar ⟶ is s
\end{code}

\noindent Note that an element in |IFuncs Σ (ar , s) is| is a function between setoids.

Let's define the type of $\Sigma$-algebras, with a record with two fields, one corresponding
to the interpretation of sorts, and another to the interpretation of operations:

\begin{code}
record Algebra {ℓ₁ ℓ₂ : Level}  (Σ : Signature) :
                                Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  constructor _∥_
  field
    _⟦_⟧ₛ    : ISorts {ℓ₁} {ℓ₂} Σ
    _⟦_⟧    : ∀ {ty : ΣType Σ} → (f : funcs Σ ty) → IFuncs Σ ty _⟦_⟧ₛ
\end{code}

We use a convenient notation for fields. The interpretation of sort |s| in
|A| is writed |A ⟦ s ⟧ₛ|, and the interpretation of an operation |w|, |A ⟦ w ⟧|.


We define too a type representing the domain of an interpretation of function symbol,
wich will be useful in later definitions.
If |ar| is the arity of an operation |f|, the interpretation will be a function between
setoids, with domain the heterogeneous vectors with arity |ar| and interpretation |_⟦_⟧ₛ A|:

\begin{spec}
_⟦_⟧ₛ* : ∀ {Σ} {ℓ₁} {ℓ₂}  → (A : Algebra {ℓ₁} {ℓ₂} Σ)
                          → (ar : Arity Σ) → Set _
_⟦_⟧ₛ* {Σ} A ar = Carrier (VecSet (sorts Σ) (_⟦_⟧ₛ A) ar)
\end{spec}

\medskip

Let see an example of a |Σₑ|-algebra, the semantics of the expression language that we
introduced previously.

\paragraph{Example} Let's define the |Σₑ|-algebra |Semₑ|. The elements of the carrier
will be functions from states to natural numbers. 

\begin{spec}
State : Set
State = Var → ℕ
\end{spec}


\begin{spec}
iSortsₑ : ISorts Σₑ
iSortsₑ E = State →-setoid ℕ
\end{spec}

\noindent The function |→-setoid| allows us to define a function between two trivial
setoids, where the equivalence relation is the extensional equality.

Let's define the interpretation of each operation. Like we saw previously, a function
between setoids consists of two fields: the function of carriers, and de proof of
congruence (if two elements are related, the elements resulting of applying the function
are related too). We ommit this proof in this text.

For each |n : ℕ| we have an operation |valN n|. The arity is empty and the target sort is
|E|:

\begin{spec}
iValN : (n : ℕ) → IFuncs Σₑ ([] , E) iSortsₑ
iValN n = record  { _⟨$⟩_ = λ { ⟨⟩ σ → n }
                  ; cong = ... }
\end{spec}

The operation |plus| have type |(E ∷ [ E ] , E)|. So, the interpretation will be a
function from vectors of two elements of type |State → ℕ| to |State → ℕ|:

\begin{spec}
iPlus : IFuncs Σₑ (E ∷ [ E ] , E) iSortsₑ
iPlus = record  { _⟨$⟩_ = λ { (v₀ ▹ v₁ ▹ ⟨⟩) σ → v₀ σ + v₁ σ }
                ; cong = ... }
\end{spec}

By last, for each variable |v| we have an operation |varN v|, with empty arity and
target sort |E|. The interpretation is a function from empty vectors (corresponding to
empty arity) to |State → ℕ| (corresponding to the interpretation of |E|). This function
is the application of state to the variable |v|:

\begin{spec}
iVarN : (v : Var) → IFuncs Σₑ ([] , E) iSortsₑ
iVarN v = record  { _⟨$⟩_ = λ { ⟨⟩ σ → σ v }
                  ; cong = ... }
\end{spec}

So, we can define the |Semₑ| algebra:

\begin{spec}
iFuncsₑ : ∀ {ty} → (f : funcs Σₑ ty) → IFuncs Σₑ ty iSortsₑ
iFuncsₑ (valN n) = iValN n
iFuncsₑ plus = iPlus
iFuncsₑ (varN v) = iVarN v
\end{spec}

\begin{spec}
Semₑ : Algebra Σₑ
Semₑ = iSortsₑ ∥ iFuncsₑ
\end{spec}

\subsection*{Homomorphism}

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
t₁ : HU Σₑ E
t₁ = term (valN 2) ⟨⟩

t₂ : HU Σₑ E
t₂ = term (varN " x ") ⟨⟩

t₃ : HU Σₑ E
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

