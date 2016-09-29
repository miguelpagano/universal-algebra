\section{Conclusions}

We have formalized an initial part of universal algebra
and we use this formalization to develop a framework of correct translation,
in Agda. In order to define a correct translator within this framework,
one must to define signatures describing grammatical categories and
operators of each language, algebras defining the semantics and
an interpretation of the source signature in the target signature,
wich describes the translator. Finally, defining an homomorphism
between the semantics completes the proof of correction.
A complete example of the development of a compiler of a simple
expression language, with variables, into a stack-based machine language
illustrates the use of the framework.

There are some works on formalization of algebra and universal algebra (citar?),
but as far as we know, there isn't a definition in type theory of translation of signatures
in the current bibliography. The formalization that we present includes a definition
of the concept of \textit{derived signature morphism} and it's possible to define
a certified correct translator from the specification of the languages and their semantics,
like we have shown in the example on section 4.

We are currently extending the formalization of universal algebra, defining other concepts
like congruences, subalgebra and proving theorems. We want to continue defining
equational calculus and rewriting.
On the other hand, we want to define others examples of translation into the
algebraic framework that we developed in this work, and we are working
on other frameworks to develop correct compilers into
type theory.


%% In this work we intended to study two topics. On the one hand,
%% formalization of universal algebra, and on the other,
%% the application of concepts of universal algebra to prove correction of compilers.

%% Trabajos existentes en formalización de algebras
%% There are some works of formalization of algebra in type theory. In \cite{jackson1994exploring}
%% , \cite{yu2003formalizing}, \cite{mortberg2014formalizing} are defined enough concepts to
%% work with rings, groups, fields, monoids, etc. Universal algebra allows to reason about
%% algebraic structures in a general way, and 

%% With Universal algebra is possible
%% to reason about posibilit 



%% Por qué es interesante tener formalizado. Muchos problemas en
%% ciencias de la computación pueden modelarse con universal algebra y
%% teniendo una formalización pueden estudiarse propiedades y distintos problemas
%% como el del compilador correcto que mostramos en este trabajo. Razonar sobre...
%% 

%% {- corrección de compiladores con álgebra universal. Importancia de ese enfoque,
%% tenerlo formalizado permite blabla -}






\label{sec:conclusions}
