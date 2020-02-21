\section{Conclusions}
\label{sec:conclusions}

As far as we know, heterogeneous universal algebra has not attracted a
great interest in the academic community of type theory. In this
paper, we have developed in Agda a library with the main concepts of
heterogeneous universal algebra, up to the proof of three isomorphisms
theorems and the freenes of the term algebra over a set of
variables. In order to define the term algebra we have introduced
heteregeneous vectors, which later turned out to be very useful in other
parts of the library, for example as the set of axioms of finite
theories and as premises of deduction rules.

We further introduced a formal systems for conditional equational
logic and prove its soundness and completeness with respect to Goguen
and Messeguer satisfaction of multi-sorted equations. As a minimal
example, we used this system to prove some theorems of (some)
axiomatization of boolean algebras.

Finally, we defined a novel representation for (derived) signature
morphisms and its associated contra-variant functor on algebras. We
also show that, under some restrictions, this functor also preserves
models.

We think that this development opened the path to several further
work, in particular:
\begin{enumerate*}[label=(\roman*),itemjoin={}]
\item a natural step is to allow several deduction systems (leading to
  a formalization of institutions);
\item consider algebras of binding structures as proposed by \cite{fiore-2010};
\item introduce multi-sorted rewriting;
\item formalize more of the mathematical theory behind universal algebra, for
  example Birkhoff's (quasi)-variety characterization; 
\item explore the idea of using completeness and soundness for
  automating the proof of identities in algebraic structures; %braibant phd
\item put the library at work by specifying abstract data types.
\end{enumerate*}



% We have formalized in Agda some heterogeneous universal algebra and
% use it to develop a framework of correct translation. In order to get
% a correct translator within this framework, one must, first, define
% signatures describing the grammatical categories and operators of each
% language, then algebras prescribing the semantics, and a translation
% from the source signature to the target signature. To get the proof of
% correctnes one has to provide a homomorphism between the semantics. We
% illustrate this framework with the development of a compiler of a
% simple expression language, with variables, into a stack-based machine
% language illustrates the use of the framework.

% Although there are much work done on formalization of algebraic
% results in type theory, we have found only two formalization of
% heterogeneous universal algebra, namely Capretta's and Kahl's already
% cited works. Moreover, as far as we know, there is no literature about
% definitions in type theory of translations of signatures. Our
% development includes such a notion which corresponds to the concept of
% \textit{derived signature morphism}. As we have shown, this is the key
% concept for getting certified correct translator from the
% specification of the languages and their semantics.

% We are currently extending the formalization of universal algebra,
% defining other concepts like congruences, subalgebra and proving the
% homomorphism theorems. We also want to continue defining equational
% calculus and rewriting, aiming at a formalization of rewriting logic.
% Independently, it seems interesting to see how far other work on using
% algebraic methods for compilers can be formalized; ideally, we would
% like to study Meijer's \citeyear{meijer-92} advice on improving
% compilers. 
