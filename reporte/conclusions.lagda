\section{Conclusions}
\label{sec:conclusions}

We have formalized in Agda some heterogeneous universal algebra and
use it to develop a framework of correct translation. In order to get
a correct translator within this framework, one must, first, define
signatures describing the grammatical categories and operators of each
language, then algebras prescribing the semantics, and a translation
of the source signature in the target signature. To get the proof of
correctnes one has to provide a homomorphism between the semantics. We
illustrate this framework with the development of a compiler of a
simple expression language, with variables, into a stack-based machine
language illustrates the use of the framework.

Although there are much work done on formalization of algebraic
results in type theory, we have found only two formalization of
heterogeneous universal algebra, namely Capretta's and Kahl's already
cited works. Moreover, as far as we know, there is no literature about
definitions in type theory of translations of signatures. Our
development includes such a notion which corresponds to the concept of
\textit{derived signature morphism}. As we have shown, this is the key
concept for getting certified correct translator from the
specification of the languages and their semantics.

We are currently extending the formalization of universal algebra,
defining other concepts like congruences, subalgebra and proving the
homomorphism theorems. We also want to continue defining equational
calculus and rewriting, aiming at a formalization of rewriting logic.
Independently, it seems interesting to see how far other work on using
algebraic methods for compilers can be formalized; ideally, we would
like to study Meijer's \citeyear{meijer-92} advice on improving
compilers. 

\paragraph{Acknowledgments} We are grateful to Alberto Pardo and
Marcos Viera for inviting us to Montevideo to collaborate on (yet)
another approach for constructing correct compilers.
