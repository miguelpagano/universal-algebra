\documentclass[10pt]{sigplanconf}

% The following \documentclass options may be useful:

% preprint      Remove this option only once the paper is in final form.
% 10pt          To set in 10-point type instead of 9-point.
% 11pt          To set in 11-point type instead of 9-point.
% numbers       To obtain numeric citation style instead of author/year.

\usepackage{amsmath}
\usepackage{mathpartir}
\usepackage{tikz}
\usepackage{ upgreek }
\usepackage[bookmarksopen,
bookmarksdepth=2,
breaklinks=true
colorlinks=true,
urlcolor=blue]{ hyperref }
%format VecH' = Vec
%format HVec  = Vec
%format 〉 = ")"
%format 〈 = "("
%format ⟨⟨ = "\langle\!"
%format ⟩⟩ = "\!\rangle"

%format _≈→_ = "\ensuremath{\_≈_{\mathit{ext}}\_}"
%format ≈→ = "\ensuremath{≈_{\mathit{ext}}}"
%format Equiv≈→ = "\ensuremath{\mathsf{Equiv}≈_{\mathit{ext}}}"

%format _≈A_ = "\ensuremath{≈_{A}}"
%format _≈B_ = "\ensuremath{≈_{B}}"
%format ≈A = "\ensuremath{≈_{A}}"
%format ≈B = "\ensuremath{≈_{B}}"
%format |T| = "\ensuremath{\mathcal{T}}"
%format |Tc| = "\ensuremath{\mathcal{T}_m}"
%format ∣h∣→A = |h|
%format map|h|→A = map|h|
%format |h|A = |H|
%format |h'|A = H

%% "\ensuremath{h_{A}}"
%% "\ensuremath{h_{A}^{\ast}}"

%include agda.fmt
%include unicode.fmt
\DeclareUnicodeCharacter{7504}{\ensuremath{^{m}}}
\DeclareUnicodeCharacter{10140}{\ensuremath{\Rightarrow}}
\DeclareUnicodeCharacter{10035}{\ensuremath{\ast}}
\DeclareUnicodeCharacter{8338}{\ensuremath{_{o}}}
\DeclareUnicodeCharacter{7506}{\ensuremath{^{o}}}
\DeclareUnicodeCharacter{8407}{\ensuremath{^{\rightarrow}}}
\DeclareUnicodeCharacter{12296}{(}
\DeclareUnicodeCharacter{12297}{)}
\newcommand{\cL}{{\cal L}}
\newcommand{\ie}{i.e.\@@ }
\newcommand{\manu}[1]{#1}

\begin{document}

\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}
\conferenceinfo{CPP '17}{January 16--17, 2017, Paris, France}
\copyrightyear{2017}
\copyrightdata{978-1-nnnn-nnnn-n/yy/mm}
\copyrightdoi{nnnnnnn.nnnnnnn}

% Uncomment the publication rights you want to use.
%\publicationrights{transferred}
%\publicationrights{licensed}     % this is the default
%\publicationrights{author-pays}

%\titlebanner{banner above paper title}        % These are ignored unless
\preprintfooter{short description of paper}   % 'preprint' option specified.

\title{Certified Compilation via Universal Algebra}

\authorinfo{Emmanuel Gunther}
           {FaMAF, UNC - CONICET}
           {gunther@@famaf.unc.edu.ar}
\authorinfo{Miguel Pagano}
           {FaMAF, UNC}
           {pagano@@famaf.unc.edu.ar}
\authorinfo{Alejandro Gadea}
           {FaMAF, UNC - CONICET}
           {gadea@@famaf.unc.edu.ar}

\maketitle

\begin{abstract}
  An interesting approach to construct correct compilers is given by
  the framework of heterogeneous algebras. Although this is a
  fairly old approach, we could not find any formalization in type
  theory of this methodology.  Indeed, there seems that universal
  algebra did not attracted a lot of attention in type theory.
 
  In this work, we formalize in Agda enough universal algebra in order
  to define languages and their semantics via initial algebra
  semantics. The key notion to get a correct compiler within this
  approach is to be able to translate algebras of the target signature
  to the source signature. This concept is known as \emph{derived
  signature morphism}, and as far as we know, this is the first
  formalization in type-theory of it.

\end{abstract}

\category{D.3.1}{Programming Languages}{Formal Definitions and Theory}
\category{F.3.1}{Specifying and Verifying and Reasoning about Programs}{Mechanical Verification}
\category{F.3.2}{Semantics of Programming Languages}{Algebraic approaches to semantics}
\category{D.3.4}{Processors}{Compilers}
% general terms are not compulsory anymore,
% you may leave them out
% \terms


\keywords
correct compiler, universal algebra, formalization of mathematics

%include introduction.lagda
%include univ-alg.lagda
%include transforming-algebras.lagda
%include compiler.lagda
%include conclusions.lagda


\bibliographystyle{plainnat}
\bibliography{biblio}


\end{document}
