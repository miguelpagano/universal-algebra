\section{Conclusions}
\label{sec:conclusions}

As far as we know, heterogeneous universal algebra has not attracted a
great interest in the academic community of type theory. In this
paper, we have developed in Agda a library with the main concepts of
heterogeneous universal algebra, up to the proof of the three
isomorphisms theorems and the freeness of the term algebra over a set
of variables. In order to define the term algebra we have introduced
heterogeneous vectors, which later turned out to be very useful in
other parts of the library, for example as the set of axioms of finite
theories and as premises of deduction rules. We further introduced a
formal system for conditional equational logic and proved its
soundness and completeness with respect to Goguen and Meseguer
semantics (we refer the reader to \cite{vidal-06} for a deeper
explanation of this result recasting it on a categorical
setting). Finally, we defined a novel representation for (derived)
signature morphisms and its associated contra-variant functor on
algebras. We also showed that, under some restrictions, this functor
also preserves models.

\textit{Related Work.} Let us contrast our work with other
formalizations covering some aspects of universal algebra. As far as
we know, since Capretta's \cite{capretta-99} first mechanization of
universal algebra and its further extension to equational logic in his
thesis, the closest new works are Kahl's \cite{kahl-2011}
formalization of allegories and the development of the algebraic
hierarchy lead by Spitters \cite{spitters-algebraic-11}. Capretta
considered only finitary signatures and his work does not encompass
signature morphisms. Spitters and his co-workers developed some very
preliminary definitions of universal algebra, because their goal is to
use the notion of variety to define the algebraic hierarchy up to the
construction of the reals; in particular they use Coq's typeclasses to
have a cleaner representation of algebraic structures.


\textit{Future Work.} We think that this development opened the path
to several further work, in particular:
\begin{enumerate*}[label=(\roman*),itemjoin={}]
\item a natural step is to formalize institutions;
\item consider algebras of binding structures as proposed by Fiore
\cite{fiore-2010}, Capretta's and Felty's formalization \cite{capretta/felty:2009}
of higher-order algebras might be an interesting starting point;
\item introduce multi-sorted rewriting;
\item formalize more of the mathematical theory behind universal algebra, for
  example Birkhoff's (quasi)-variety characterization; and
\item explore the idea of using completeness and soundness for
  automating the proof of identities in algebraic structures. %braibant phd
\end{enumerate*}

\begin{ack}
  We are grateful to the anonymous referees for their careful reading
  and suggestions.
\end{ack}
