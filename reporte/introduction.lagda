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
high-level semantics to the low-level one (or viceversa). In this work we formalize
enough heterogenous universal algebra in order to complete the
definition of a correct compiler. Throughout the article we will use
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

% TODO: cambiar \Sigma por \mathit{State}, así ahorramos el clash con signaturas.
\newcommand{\state}{\mathit{State}}
\newcommand{\evalExpr}{\mathit{eval}}

The intended semantics for the source language is a function mapping
states to natural numbers; let $\state = X \to \mathbb{N}$ and $\sigma$ a
meta-variable over $\state$, the semantics is given by:
\begin{equation*}
\begin{array}{lllcl}
  &\multicolumn{4}{l}{\evalExpr \colon\ \expr \to \state \to \mathbb{N}}\\
  &\evalExpr &n                &=&\lambda\,\sigma \rightarrow n\\
  &\evalExpr &v                &=& \lambda\,\sigma \rightarrow \sigma\,v\\
  &\evalExpr &(e_1 \oplus e_2) &=& \lambda\,\sigma \rightarrow (\evalExpr\,e_1\,\sigma) + (\evalExpr\,e_2\,\sigma)
\end{array}%
\end{equation*}

\newcommand{\stack}{\mathit{Stack}}
\newcommand{\execCode}{\mathit{exec}}
%TODO: poner referencias para lo habitual respecto a low-level languages.
%TODO: llamar la atención sobre la parcialidad de exec!
Semantics of Low-level languages are usually given as a transition
relation between configurations of the (abstract) machine. If the
relation is deterministic, then one can infer a big-step semantics and
from that a functional semantics as proposed by
\citet{owens2016bigstep}. An initial configuration of our machine is
a pair $(s, \sigma)$ of a stack of numbers and a state, while the final
configuration is a stack $s'$. We assume that $\stack$s are lists of numbers. 
\newcommand{\consop}{\,\colon\!\!\!\colon}
\[
\begin{array}{lllcl}
  &\multicolumn{4}{l}{\execCode \colon \code \rightarrow \stack \times \state \rightarrow \stack}\\
  &\execCode &(\instr{push}\,n)     &=&\lambda\,(s , \sigma) \rightarrow (n \consop s)\\
  &\execCode &(\instr{load}\,v)     &=&\lambda\,(s , \sigma) \rightarrow (\sigma\,v \consop s)\\
  &\execCode &(c_1\,;\,c_2) &=&\lambda\,(s , \sigma) \rightarrow \execCode\;c_2\;(\execCode\;c_1\;(s,\sigma),\sigma)\\
  &\execCode &\instr{add}   &=&\lambda\,(n  \consop  m  \consop  s , \sigma) \rightarrow (n \, + \, m  \consop s)\\
\end{array}
\]
\newcommand{\comp}{\mathit{comp}}

A compiler $\comp \colon \expr \rightarrow \code$ is correct if for
every expression $e$ the generated code $\comp\,e$ has the ``same''
semantics of $e$. In our setting we can state correctness formally as
\[
  \execCode\,(\comp\,e)\,(s,\sigma)\,=\,\evalExpr\,e\,\sigma \consop s \enspace .
\]
It is straightforward to write a compiler and then prove its correctness by induction
on the structure of expressions (we omit this proof):
\[
\begin{array}{lllcl}
  &\multicolumn{4}{l}{\comp \colon \expr \rightarrow \code}\\
  &\comp &n  & = &  push\,n\\
  &\comp &v  & = & load\,v\\
  &\comp &(e_1 \oplus e_2) & = & \comp\,e_2\,;\,\comp\,e_1\,;\,add
\end{array}
\]

\paragraph{The Algebraic Perspective} 
Under the algebraic perspective, one does not start from an abstract
grammar but only from a signature which defines the grammatical
categories (sorts in the algebraic parlance) and the operators
(terminals) together with their arities. The language corresponding to
a signature $\Sigma_e$ is the \emph{term algebra} and it consists of
the phrases freely generated from the operators. A semantics is
nothing more than a algebra for the signature, which is completely
determined by choosing an interpretation for (the sorts and) the
operators.

\newcommand{\hsem}[1]{\mathit{hsem}(#1)}
In our case we have two (monosorted) signatures $\Sigma_e$ and
$\Sigma_c$ giving rise to their term algebras $T_e$ and $T_c$,
respectively. We interpret the only sort of $\Sigma_e$ as the set of
total functions $\mathit{Sem} = \state \to \mathbb{N}$.
%TODO: 
% - poner la interpretación de símbolos para uno de los lenguajes
% - casi no hablamos de homomorfismos hasta ahora! 
 Once we choose an interpretation of the symbols we get, by a general
result about algebras, the denotation of each phrase. For instance,
from the following interpretation of the operators:
\[
  \begin{array}{lcl}
    i(n)()&=&\lambda \sigma \mapsto n\\
    i(x)()&=&\lambda \sigma \mapsto \sigma\,x\\
    i(\oplus)(f,g)&=&\lambda \sigma \mapsto f\,\sigma + g\,\sigma
  \end{array}
\]
we get a unique homomorpism $\mathit{hsem} \colon T_e \to \mathit{Sem}$
satisfying:
\[
  \begin{array}{lcl}
    \hsem{n}&=&\lambda \sigma \mapsto n\\
    \hsem{x}&=&\lambda \sigma \mapsto \sigma\,x\\
    \hsem{e_1 \oplus e_2}&=&\lambda \sigma \mapsto \hsem{e_1}\,\sigma + \hsem{e_2}\,\sigma
  \end{array}
\]
In parallel, we interpret the sort of $\Sigma_c$ as the set of partial
functions from $\mathit{Exec} = \stack\times\state \to \stack$ and an
intepretation for the symbols of $\Sigma_C$ leads to the semantics
$\mathit{hexec} \colon T_C \to \mathit{Exec}$. We can picture the situation so far as: 

\begin{center}
  \begin{tikzpicture}[>=latex]
    \node (te) at (0,1.5) {$T_e$}; 
    \node (tc) at (3,1.5) {$T_c$}; 
    \node (seme) at (0,0) {$\mathit{Sem}$} ; 
    \node (semc) at (3,0) {$\mathit{Exec}$} ; 
    \path [->,shorten <=2pt,shorten >=2pt] (te) edge node [left] {$\mathit{hsem}$} (seme); 
    \path [->,shorten <=2pt,shorten >=2pt] (tc) edge node [right] {$\mathit{hexec}$} (semc);
  \end{tikzpicture}
\end{center}

%TODO: poner las referencias en las conclusiones en un apartado sobre
% related work? Ahora corta mucho la lectura.

Instead of defining ingeniously the translation $\comp$ and proving
afterwards its correctness, we will obtain it from a more broader
construction which will transform each algebra $A$ of $\Sigma_C$ into
an algebra $\widetilde{A}$ of $\Sigma_e$ and also each homomorphism from
$h \colon A \to B$ into an homomorphism $\widetilde{h}\colon \widetilde A
\to \widetilde B$. These transformations will arise from a
\emph{signature-translation} from $\Sigma_e$ to $\Sigma_C$. This concept
is related with the interpretability of similarity types in universal algebra (cf.\
\cite{garcia-84}), and it is called in different ways in the literature:
\citet{fujiwara-1959} introduced this notion as \textit{mappings
between algebraic systems}, \citet{janssen-98} called it a
\textit{polynomial derivor} and \citet{mossakowski-15} refer to it as
a \textit{derived signature morphism}, a generalization of the more
restricted \textit{signature morphisms} in the theory of institutions
\cite{goguen-92}. Translations of signatures were
analyzed categorically by \citet{fiore-2010} for second order
signatures and by \citet{vidal-2012} for first order signatures.


The transformation brings the right side of the above diagram to the
world of $\Sigma_e$ algebras, thus $\comp$ arises as the unique
homomorphism from $T_e$ to $\widetilde{T_C}$. Correctness of the compiler
follows abstractly as soon as we provide either an homomorphism
$\mathit{dec} \colon \widetilde{\mathit{Exec}} \to \mathit{Sem}$ (as
proposed by \citet{morris-73}) or an homomorphism
$\mathit{enc} \colon \mathit{Sem} \to \widetilde{\mathit{Exec}}$ (after \cite{thatcher-80}).

\begin{center}
  \begin{tikzpicture}[>=latex]
    \node (te) at (0,1.5) {$T_e$}; 
    \node (tc) at (3,1.5) {$\widetilde{T_c}$}; 
    \node (seme) at (0,0) {$\mathit{Sem}$} ; 
    \node (semc) at (3,0) {$\widetilde{\mathit{Exec}}$} ; 
    \path [->,shorten <=2pt,shorten >=2pt] (te) edge node [above] {$\mathit{comp}$} (tc); 
    \path [->,shorten <=2pt,shorten >=2pt] (te) edge node [left] {$\mathit{hsem}$} (seme); 
    \path [->,shorten <=2pt,shorten >=2pt] (tc) edge node [right] {$\widetilde{\mathit{hexec}}$} (semc);
    \path [->,shorten <=2pt,shorten >=2pt] (seme.10) edge node [above] {$\mathit{enc}$} (semc.170);
    \path [->,shorten <=2pt,shorten >=2pt] (semc.190) edge node [below] {$\mathit{dec}$} (seme.350);
  \end{tikzpicture}
\end{center}

\paragraph{Outline}

In Sect. \ref{sec:univ-alg} we present our formalization in
constructive type-theory of enough universal algebra, both concepts
and results. We discuss our design implementation in Agda and compare
it with other formalizations, in particular \citeauthor{capretta-99}'s
in Coq.

In Sect. \ref{sec:trans} we introduce the concept of \emph{signature-translation}
and prove that it induces a transformation of algebras
and their homomorphisms. As far as we know, there is no formalization
of heterogeneous algebras including these results.

Instantiating the abstract framework developed in the previous
sections, we proceed to formalize in Sect. \ref{sec:compiler} the
example shown in this introduction.

Finally, we conclude in Sect. \ref{sec:conclusions} by discussing
advantages and shortcomings of the algebraic construction of compilers,
and pointing out possible future directions, specially concerning the
formalization of universal algebra.
