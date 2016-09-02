\section{Introduction}

The pioneering work by \citet{mccarthy1967correctness} on
a correct compiler for arithmetic expressions was followed by a myriad
of further papers, and even books, about how to prove the correctness
of compilers and also methodologies for constructing correct compilers.
% TODO:
% - completar con trabajos: Burstall
% - mencionar CompCert (es lo más)
% - mencionar Hutton (es nuevo, es cercano?)
One early approach for structuring the proof of correctness proposed
by \citet{morris-73} used universal algebra (particularly
heterogeneous algebras \citet{birkhoff-70}). Soon after the ADJ group
popularized the use of universal algebra contributing the notion of
\emph{initial algebra sematics} \citet{goguen-77} and expanded
\cite{thatcher-80} Morris' work. %TODO: en qué sentido?
% TODO: Es un salto medio grande del 80 al 98, quizás lo podamos
% rellenar un poco? 
% - Meijer
% - Rus?
More recently \citet{janssen-98} proposed to use this algebraic framework
more broadly, taking compilation as a particular case of a translation.

The main idea behind this algebraic proof of correctness is to
conceive both languages, source and target, as the initial algebras of
their respective signatures; semantics of the languages are freely
obtained by initiality after giving an interpretation for the
corresponding function symbols. The trick to get correctness is
to map the target language and its semantics as algebras for
the source language and then provide an homomorphism from the
high-level semantics to the low-level one. In this work we formalize
enough heterogenous universal algebra in order to complete the
definition of a correct compiler. Throgout the article we will use
McCarthy and Painter's language as a guiding example.
% TODO: Sería bueno encontrar una forma más vendedora para decir lo
% que hacemos y también estaría muy bien si tenemos una formalización
% del lenguaje imperativo simple, aunque no lo mostremos.



\newcommand{\expr}{\langle \mathit{expr}\rangle}
\newcommand{\code}{\langle \mathit{code}\rangle}
\newcommand{\instr}[1]{\mathsf{#1}}
\paragraph{Source and target languages} The source language consists
of natural constants, variables and addition. Let $X$ be a countable
set of variables. Let $x,y,z$ be meta-variables over $X$ and $m,n$
over $\mathbb{N}$.
% TODO: por qué no tener las signaturas como funtores que dado un conjunto
% de variables, genera la sintaxis?
\begin{align*}
    \expr \ni e,e' &::=\ n\ \mid\ x\ \mid e ⊕ e'
\intertext{The target language consists of a sequence of instructions for a stack-machine.}
  \code \ni c,c' & ::=  \instr{push}\,n \ \mid\ \instr{load}\,x \ \mid\ c\,;\, c' \ \mid\ \instr{add}
\end{align*}

\newcommand{\state}{\Sigma}
\newcommand{\evalExpr}{\mathit{eval}}

The intended semantics for the source language is a function mapping
states to natural numbers; let $\state = X \to \mathbb{N}$ and $\sigma$ a
meta-variable over $\state$, the semantics is given by:
\begin{equation*}
\begin{array}{lllcl}
  &\multicolumn{4}{l}{\evalExpr \colon\ \expr \to \state \to \mathbb{N}}\\
  &\evalExpr &n                &=&\lambda\,\upsigma \rightarrow n\\
  &\evalExpr &v                &=& \lambda\,\upsigma \rightarrow \upsigma\,v\\
  &\evalExpr &(e_1 \oplus e_2) &=& \lambda\,\upsigma \rightarrow (\evalExpr\,e_1\,\upsigma) + (\evalExpr\,e_1\,\upsigma)
\end{array}%
\end{equation*}


\newcommand{\stack}{\mathit{Stack}}
\newcommand{\execCode}{\mathit{exec}}
%TODO: poner referencias para lo habitual respecto a low-level languages.
Low-level languages semantics are usually given as a transition
relation between configurations of the (abstract) machine. If the
relation is deterministic, then one can infer a big-step semantics and
from that a functional semantics as proposed by
\citet{owens2016bigstep}. An initial configuration of our machine is
a pair $(s, \upsigma)$ of a stack of numbers and a state, while the final
configuration is a stack $s'$. We assume that $\stack$s are lists of numbers. 
\newcommand{\consop}{\,\colon\!\!\!\colon}
\[
\begin{array}{lllcl}
  &\multicolumn{4}{l}{\execCode \colon \code \rightarrow Stack \times State \rightarrow Stack}\\
  &\execCode &(\instr{push}\,n)     &=&(s , \upsigma) \rightarrow (n \consop s)\\
  &\execCode &(\instr{load}\,v)     &=&\lambda\,(s , \upsigma) \rightarrow (\upsigma\,v \consop s)\\
  &\execCode &(c_1\,;\,c_2) &=&\lambda\,(s , \upsigma) \rightarrow \execCode\;c_2\;(\upsigma,\execCode\;c_1\;(\upsigma,s))\\
  &\execCode &\instr{add}   &=&\lambda\,(n  \consop  m  \consop  s , \upsigma) \rightarrow (n \, + \, m  \consop s)\\
\end{array}
\]

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
de dos signaturas $\Sigma_e$ y $\Sigma_c$, obteniendo sus álgebras de
términos $T_e$ y $T_c$. Los dominios semánticos, digamos $Sem$ y
$Exec$, serán álgebras de cada signatura respectivamente. En el primer
caso cada elemento del carrier del álgebra $Sem$ será una función con
tipo $State \rightarrow \mathds{N}$, en el segundo una función con
tipo $Stack \times State \rightarrow Stack$. Las semánticas quedan
determinadas por el único homomorfismo que existe entre el álgebra de
términos y cada álgebra, por inicialidad. Tenemos entonces el
siguiente diagrama:

\begin{diagram}
  T_e     &     &   &  &    &T_c\\
  \dTo_{hsem} &     &   &  &   &\dTo_{hexec}\\
  Sem      &     &   &  &    &Exec\\
\end{diagram}

La clave del enfoque consiste en poder ver a las álgebras (y
homomorfismos) de la signatura $\Sigma_c$ como álgebras (y
homomorfismos) de la signatura fuente $\Sigma_e$, para ello
introduciremos el concepto de \textit{transformador de álgebras}
(similar a \textit{polynomial derivor}, que nombra Janssen, o
\textit{derived signature morphism} en teoría de instituciones,
\cite{mossakowski-15}).  Si $A$ es una $\Sigma_c$-álgebra, llamemos
$A\sim$ a su transformada en $\Sigma_e$. Tenemos entonces el siguiente
diagrama:

\begin{diagram}
  T_e     &\rTo^{comp}    &T_c\sim\\
  \dTo_{hsem} & &\dTo_{hexec\sim}\\
  Sem      &  &Exec\sim\\
\end{diagram}

El compilador queda definido por el único homomorfismo que existe
entre $T_e$ y $T_c\sim$.  Si podemos definir un homomorfismo $enc$ (o
$dec$) entre $Sem$ y $Exec\sim$ (o viceversa), el diagrama conmuta por
inicialidad de $T_e$:

\begin{diagram}
  T_e     &\rTo^{comp}    &T_c\sim\\
  \dTo_{hsem} & &\dTo_{hexec\sim}\\
  Sem      & \pile{\rTo^{enc} \\ \lTo_{dec}}   &Exec\sim\\
\end{diagram}

\paragraph{Organización del texto}

En la segunda sección de este artículo formalizamos los conceptos de
signatura, álgebra, homomorfismo, inicialidad y álgebra de términos,
obteniendo una librería en Agda para el uso de álgebras universales en
general. Se discuten algunas decisiones de implementación. El
resultado es similar al que obtiene Venanzio Capretta en
\cite{capretta-99}.

En la tercera sección introducimos el concepto de transformación de
álgebras, para llevar álgebras de la signatura target a la signatura
source, y probamos que los homomorfismos se preservan. Este concepto
no está en la bibliografía existente sobre formalización de álgebras
universales.

En la cuarta sección damos el ejemplo completo del compilador de un
lenguaje de expresiones aritméticas simple presentado anteriormente,
utilizando el framework.
