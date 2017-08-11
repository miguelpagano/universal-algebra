\section{Introduction}

Universal algebra~\cite{birkhoff-1935} is the study of different types
of algebraic structures at an abstract level, thus revealing common
results which are valid for all of them and also allowing for a
unified definition of constructions (for example, products,
sub-algebra, congruences). Universal algebra has played a relevant
role in computer science since its earliest days, in particular the
seminal paper of Birkhoff~\cite{birkhoff-70} features regular
languages as a prominent example; shortly before,
Burstall~\cite{burstall69} had proved properties of programs using
structural induction, by conceiving the language as an
initial algebra. The ADJ group~\cite{goguen-adj} promoted multi-sorted algebras as a
key theoretical tool for specifying data
types~\cite{adj-abstract-data-types}, semantics~\cite{goguen-77}, and
compilers~\cite{thatcher1981more}.  More recently,
institutions~\cite{goguen-92}, a generalization of universal algebra,
has been used as a foundation of methodologies and frameworks for
software specification and development~\cite{sannella2012foundations}.

In spite of the rich mathematical theory of heterogeneous algebras
(mostly inherited from the monosorted setting, but not always
\cite{tarlecki-nuances}), there are few publicly available
formalizations in type theory (which we discuss in the conclusion).
This situation is to be contrasted with impressive advances in
mechanization of particular algebraic structures as witnessed, for
example, by the proof of the Feit-Thompson theorem in Coq by Gonthier
and his team~\cite{gonthier2013machine}.

In this work we present an Agda library of multi-sorted universal
algebra aiming both a reader with a background in the area of
algebraic specifications and also the community of type theory.  For
the former, we try to explain enough Agda in order to keep the paper
self-contained; we will recall the most important definitions of
universal algebra. The main contributions of this paper are:
\begin{enumerate*}[label=\ (\roman*),itemjoin={}]%
\item the first formalization of basic universal algebra in Agda;
\item the first, to our knowledge, formalization in type theory of
  derived signature morphisms and the reduct algebras induced by them;
\item a novel representation of heterogeneous signatures in
  type theory, where operations are modelled using sets indexed by
  arities; and
\item an independent library of heterogeneous vectors.
\end{enumerate*}
We formalized the proof that the term algebra is initial and also the
proofs of the three isomorphism theorems; moreover we also define a
deduction system for conditional equational logic and prove its
soundness and completeness with respect to Goguen and Meseguer semantics~\cite{GoguenM82}.
We also showed that the translations of
theories arising from derived signature morphisms induces a
contra-variant functor between models.  In the complete development,
which is available at
\url{https://cs.famaf.unc.edu.ar/~mpagano/universal-algebra/}, we
include several examples featuring both the use of equational
reasoning and the preservation of models by signature morphisms.

% We include several examples of use of the
% library.  In contrast with other formalizations, we define operations
% of signatures as a family indexed by arities, which we think carries
% important benefits in the use of the library: The names of operations
% are constructors of a family of datatypes and so it's possible to
% perform pattern matching on them. Our representation of signature
% allows to define infinite sorts and operations too. Much of the
% library is based on heterogeneous vectors: while all the elements of a
% vector are of the same type, in a heterogeneous vector they can have
% different types. %\footnote{Similar to the construction proposed in %
% \url{https://lists.chalmers.se/pipermail/agda/2010/001826.html}}


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

\textit{Outline.} In Sec.~\ref{sec:univ-alg} we introduce the basic
concepts of Universal Algebra: signature, algebras and homomorphisms,
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
