\documentclass[a4paper,twoside,12pt]{article}
\usepackage{amsmath}
\usepackage{mathpartir}
\usepackage{tikz}
\usepackage[small,nohug,heads=vee]{diagrams}
\diagramstyle[labelstyle=\scriptstyle]
\usepackage{authblk}
\usepackage{natbib}
\usepackage{ dsfont }
\usepackage{ upgreek }
\usepackage{ hyperref }
%include agda.fmt
%include unicode.fmt

\begin{document}

\title{Formalización de un framework algebraico para
       traducción correcta de lenguajes}

\author{Emmanuel Gunther}
\affil{FaMAF, UNC}
\affil{CONICET}

\date{}
       
\maketitle

\begin{abstract}

  An interesting approach to construct correct compilers is given by
  the framework of heterogeneous universal agebras. In this work, we
  formalize in Agda enough universal algebra to get translations from
  one language to another and prove the correctness of the compilation
  by relating semantics of the source and target languages. As far as
  we know, this is the first formalization in type-theory of the
  concept of \emph{derived singature morphism}.
  

%   Un enfoque para abordar el desarrollo de traductores correctos de
%   lenguajes es mediante álgebras universales. En este trabajo
%   presentamos una formalización en teoría de tipos de un framework
%   algebraico para traducir lenguajes, realizado en el lenguaje
%   Agda. Para ello definimos conceptos básicos de álgebras universales
%   heterogéneas, como Signatura, Álgebra, Homomorfismo, llegando a
%   probar que el álgebra de términos es inicial.  Definimos también un
%   metalenguaje para traducir signaturas de manera general y damos un
%   ejemplo de un compilador de expresiones a un lenguaje de máquina
%   sencillo que manipula un stack.

\end{abstract}
%include introduction.lagda
%include univ-alg.lagda
%include transforming-algebras.lagda
%include compiler.lagda
%include conclusions.lagda


\bibliographystyle{plainnat}
\bibliography{biblio}


\end{document}
