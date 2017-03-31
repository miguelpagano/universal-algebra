\documentclass{llncs}

% The following \documentclass options may be useful:

% preprint      Remove this option only once the paper is in final form.
% 10pt          To set in 10-point type instead of 9-point.
% 11pt          To set in 11-point type instead of 9-point.
% numbers       To obtain numeric citation style instead of author/year.

\usepackage{amsmath}
\usepackage{mathpartir}
\usepackage{ upgreek }
\usepackage[numbers]{natbib}
\usepackage{minted}
\usemintedstyle{friendly}
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

%format Ȧ = "\ensuremath{\mathcal{A}}"
%format Ḃ = "\ensuremath{\mathcal{B}}"

%format _≈A_ = "\ensuremath{≈_{A}}"
%%format (A,≈A,_) = "\ensuremath{(A,≈_{A},\_)}"
%%format (B,≈B,_) = "\ensuremath{(B,≈_{B},\_)}"
%format _≈B_ = "\ensuremath{≈_{B}}"
%format ≈A = "\ensuremath{≈_{A}}"
%format ≈B = "\ensuremath{≈_{B}}"
%format |T| = "\ensuremath{\mathcal{T}}"
%format |T|isInitial = "\ensuremath{\mathcal{T}\mathsf{isInitial}}"
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
\newcommand{\manu}[1]{\textcolor{red}{#1}}

\begin{document}

\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}


% Uncomment the publication rights you want to use.
%\publicationrights{transferred}
%\publicationrights{licensed}     % this is the default
%\publicationrights{author-pays}

%\titlebanner{banner above paper title}        % These are ignored unless


\title{Formalization of Universal Algebra}

\author{Emmanuel Gunther \and Miguel Pagano \and Alejandro Gadea}

\institute{FaMAFyC, UNC - CONICET}


%% \authorinfo{Emmanuel Gunther}
%%            {FaMAF, UNC - CONICET}
%%            {gunther@@famaf.unc.edu.ar}
%% \authorinfo{Miguel Pagano}
%%            {FaMAF, UNC}
%%            {pagano@@famaf.unc.edu.ar}
%% \authorinfo{Alejandro Gadea}
%%            {FaMAF, UNC - CONICET}
%%            {gadea@@famaf.unc.edu.ar}

\maketitle

\begin{abstract} In this work we present a novel formalization of
universal algebra in Agda. We show that heterogeneous signatures can
be elegantly modelled in type-theory using sets indexed by arities
to represent operations. We prove all the elementary results of
heterogeneous algebras, \ie that the term algebra is initial and
the three isomorphism theorems. We further internalise equational
theory and prove correctness and completeness. At the end, we define
the (derived) signature morphisms, from which we get the
contra-variant functor between algebras; moreover, we prove that the
translation of a theory induce a contra-variant functor between
models.

\end{abstract}


\keywords
universal algebra, formalization of mathematics, equational logic

%include introduction.lagda
%include univ-alg.lagda
%include equational.lagda
%include transforming-algebras.lagda
%include conclusions.lagda

\bibliographystyle{plainnat}
\bibliography{biblio}


\end{document}