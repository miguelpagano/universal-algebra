\section{Introduction}

There are many formalizations of algebraic structures in type-theory, some
achieving amazing results (Feith-Thompson). However, the development of
universal algebra in type theory is still little explored, passing nearly
two decades since the work of Capretta, with his formalization in Coq.

Universal algebra is an interesting topic from a point of view of mathematics
foundation and in computer sciences, and we offer a new formalization in Agda.
We cover all the work realized in previous work, like Capretta's, but we
improve it with novel definitions, like the way to define operations of signatures,
the formalization of signature morphisms and the benefits of use heterogeneous
vectors.

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
