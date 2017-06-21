\section{Introduction} Universal algebra has played a relevant role in
computer science since its earliest days, in particular the seminal
paper of Birkhoff \cite{birkhoff-70} features regular languages as a prominent
example; shortly before Burstall \cite{burstall69} had proved properties of
programs using structural induction, which is based on conceiving the
language as an initial algebra.  The group ADJ promoted multi-sorted
algebras as a key theoretical tool for specifying data
types\cite{adj-abstract-data-types} and for semantics
\cite{goguen-77}.
% poner cosas más nuevas: institutions, MDE? 
% uso de técnicas algebraicas para efectos?
% teorías algebraicas para binder?

In spite of the rich mathematical theory of heterogeneous algebras
(mostly inherited from the monosorted setting, but not always
\cite{tarlecki-nuances}), there are few publicly available
formalizations in type-theory (on which we comment below).  This
situation is to be contrasted with impressive advances in
mechanization of particular algebraic structures as witnessed, for
example, by the proof of the Feit-Thompson theorem in Coq by Gonthier
and his team \cite{gonthier2013machine}. 

In this work we present an Agda library of multi-sorted universal
algebra. The main contribution of this paper are:
\begin{enumerate*}[label=(\roman*),itemjoin={}]
\item the first formalization of basic universal algebra in Agda;
\item the first, to our knowledge, formalization in type-theory of
  derived signature morphisms and the reduct algebras induced by them.
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

%  is related with the interpretability of similarity types
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

\paragraph{Related Work} 

Let us contrast our work with other formalizations covering some
aspects of universal algebra (we leave aside developments which cover
some particular algebraic structure). As far as we know, since
Capretta's \cite{capretta-99} first mechanization of universal algebra
and its further extension to equational logic \cite{capretta-phd}, the
closest new works are Kahl's \cite{kahl-2011}'s formalization of
allegories and the development of the algebraic hierarchy lead by
Spitters \cite{spitters-algebraic-11,krebbers-classes-11}. Capretta
considered only finitary signatures and his work does not encompass
signature morphisms; his definition of the term algebra is a bit
awkward (it may be due to limitations of Coq at the moment). Spitters
and his co-workers developed some very preliminar definitions of
universal algebra and only proved the first isomorphism theorem,
because their goal is to use the notion of variety to define the
algebraic hierarchy up to the construction of the reals.

\paragraph{Outline} In section 2 we introduce the basic concepts of
 Universal
Algebra: Signature, algebras and homomorphisms, congruences, quotients and
subalgebras, the proofs of three isomorphisms theorems, and the proof
of the initiality of the term algebra.
In section 3 we define an equational calculus, introducing concepts of
equations, theories, satisfiability and provability, ending with the Birkhoff
proofs of soundness and completeness.
In section 4 we introduce a new representation of (derived) signature morphisms and
reduct algebras (and homomorphisms), and we explore translation and implication
of theories.
% with the property of preservation of models, under some
%restrictions.
Finally, we conclude in section 5, discussing the work done, and pointing
out possible future directions.
