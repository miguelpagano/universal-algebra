\section{Introduction}

Universal algebra \cite{birkhoff-1935} is the study of different types
of algebraic structures at an abstract level, thus revealing common
results which are valid for all of them and also allowing for a
unified definition of constructions (for example, products,
sub-algebra, congruences). Universal algebra has played a relevant
role in computer science since its earliest days, in particular the
seminal paper of Birkhoff \cite{birkhoff-70} features regular
languages as a prominent example; shortly before Burstall
\cite{burstall69} had proved properties of programs using structural
induction, which is based on conceiving the language as an initial
algebra.  The group ADJ promoted multi-sorted algebras as a key
theoretical tool for specifying data
types\cite{adj-abstract-data-types}, semantics \cite{goguen-77}, and
compilers.  In fact, our interest in formalizing universal algebra
arose when we defined in Agda a correct compiler following the
methodology proposed by ADJ. More recent connections of universal
algebra with computer science can be found in institutions as the
foundation of methodologies and frameworks for software specification
and development \cite{sannella2012foundations}.

In spite of the rich mathematical theory of heterogeneous algebras
(mostly inherited from the monosorted setting, but not always
\cite{tarlecki-nuances}), there are few publicly available
formalizations in type-theory (which we discuss in the conclusion).
This situation is to be contrasted with impressive advances in
mechanization of particular algebraic structures as witnessed, for
example, by the proof of the Feit-Thompson theorem in Coq by Gonthier
and his team \cite{gonthier2013machine}.

In this work we present an Agda library of multi-sorted universal
algebra aiming both a reader with a background in the area of
algebraic specifications and also the community of type-theory.  For
the former, we try to explain enough Agda in order to keep the paper
self-contained; we will recall the most important definitions of
universal algebra. The main contribution of this paper are:
\begin{enumerate*}[label=(\roman*),itemjoin={}]
\item the first formalization of basic universal algebra in Agda;
\item the first, to our knowledge, formalization in type-theory of
  derived signature morphisms and the reduct algebras induced by them;
\item a novel representation of heterogeneous signatures in
  type-theory, where operations are modelled using sets indexed by
  arities; and
\item an independent library of heterogeneous vectors.
\end{enumerate*}
We proved some results of heterogeneous algebras, including the proof
that the term algebra is inital and the three isomorphism theorems. We
further formalize conditional equational theory and prove soundness
and completeness. At the end, we define (derived) signature morphisms,
from which we get the contra-variant functor between algebras;
moreover, we also proved that, under some restrictions, the
translation of a theory induces a contra-variant functor between
models. In contrast with other formalization, our formalization allows
for infinitary sorts and operations and also, we think, eases the use
of the resulting library. Much of the library is based on
heterogeneous vectors: while all the elements of a vector are of the
same type, in a heterogeneous vector they can have different
types.\footnote{Similar to the construction proposed in
  \url{https://lists.chalmers.se/pipermail/agda/2010/001826.html}}



%% Mencionar qué esperamos que sepan los lectores


%is related with the interpretability of similarity types
% in universal algebra (cf.\ \cite{garcia-84}), and has an extensive
% literature: \citet{fujiwara-1959} introduced this notion as
% \textit{mappings between algebraic systems}, \citet{janssen-98},
% following the ADJ group, called it a \textit{polynomial derivor} and
% \citet{mossakowski-15} refer to it as a \textit{derived signature
% morphism}, a generalization of the more restricted \textit{signature
% morphisms} in the theory of institutions
% \cite{goguen-92}. Translations of signatures were analyzed
% categorically by \citet{fiore-2010} for second order signatures and by
% \citet{vidal-2012} for first order signatures.

\paragraph{Outline} In Sec.~\ref{sec:univ-alg} we introduce the basic
concepts of Universal Algebra: Signature, algebras and homomorphisms,
congruences, quotients and subalgebras, the proofs of three
isomorphisms theorems, and the proof of the initiality of the term
algebra.  In Sec.~\ref{sec:eqlog} we define an equational calculus, introducing
concepts of equations, theories, satisfiability and provability,
ending with the Birkhoff proofs of soundness and completeness.  In
Sec.~\ref{sec:trans} we introduce a new representation of (derived) signature
morphisms and reduct algebras (and homomorphisms), and we explore
translation and implication of theories.
% with the property of preservation of models, under some
%restrictions.
Finally, we conclude in Sec.~\ref{sec:conclusions}, discussing the
work done, and pointing out possible future directions.
