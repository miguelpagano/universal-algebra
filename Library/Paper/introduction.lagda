\section{Introduction} Universal algebra has played a relevant role in
computer science since its earliest days, in particular the seminal
paper of \citet{birkhoff-70} uses regular languages as a prominent
example.  The group ADJ promoted multi-sorted algebras as a key
theoretical tool for specifying data types, for defining the semantics
of programming languages \cite{goguen-77}, and for proving the
correctness of compilers (as already advanced by \citet{burstall69}).
In spite of its fruitful theory, there are little publicly available
formalization of heterogeneous algebras in type-theory; as far as we
know, since \citet{capretta-99} first mechanization of universal
algebra and its further extension to equational logic
\cite{capretta-eq}, the closest new work is
\citet{kahl-2011}'s formalization of allegories. This situation is
to be contrasted with impressive advances in mechanization of particular
algebraic structures as witnessed, for example, by the proof of the
Feit-Thompson theorem in Coq by \citet{gonthier2013machine}.

In this work we present a novel formalization of multi-sorted
universal algebra in Agda, where heterogeneous signatures are modelled
in type-theory using sets indexed by arities to represent operations,
in contrast to Capretta's choice of representing arities as lists of
sorts; this change allows for infinitary sorts and operations, but we
think that it also eases the use of the resulting library. In the
first part of the formalization, we proved some results of
heterogeneous algebras, including the proof that the term algebra is
initial and the three isomorphism theorems. We further formalize
conditional equational theory and prove soundness and completeness. At
the end, we define (derived) signature morphisms, from which we get
the contra-variant functor between algebras; moreover, we also proved
that, under some restrictions, the translation of a theory induces a
contra-variant functor between models.

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


\paragraph{Outline.} In section 2, we define the main concepts of Universal
Algebra: Signature, algebras and homomorphisms, congruences, quotients and
subalgebras, the proofs of three isomorphisms theorems, and the proof
of the initiality of the term algebra.
In section 3 we define an equational calculus, introducing concepts of
equations, theories, satisfactibility and provability, ending with the Birkhoff
proofs of soundness and completeness.
In section 4 we introduce a new representation of (derived) signature morphisms and
reduct algebras (and homomorphisms), and we explore translation and implication
of theories, with the property of preservation of models, under some
restrictions.
Finally, we conclude in section 5, discussing the work realized, and pointing
out possible future directions.
