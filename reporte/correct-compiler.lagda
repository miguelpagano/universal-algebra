\documentclass[preprint,10pt]{sigplanconf}

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
%format ⟨⟨ = "\langle\!"
%format ⟩⟩ = "\!\rangle"
%format ≈A = "≈_{A}"
%format ≈B = "≈_{B}"
%include agda.fmt
%include unicode.fmt

\DeclareUnicodeCharacter{10140}{\ensuremath{\Rightarrow}}
\DeclareUnicodeCharacter{10035}{\ensuremath{\ast}}
\DeclareUnicodeCharacter{8338}{\ensuremath{_{o}}}
\newcommand{\cL}{{\cal L}}
\newcommand{\ie}{i.e.\@@ }

\begin{document}

\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

\conferenceinfo{CONF 'yy}{Month d--d, 20yy, City, ST, Country}
\copyrightyear{20yy}
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

\maketitle

\begin{abstract}
  An interesting approach to construct correct compilers is given by
  the framework of heterogeneous universal agebras. In this work, we
  formalize in Agda enough universal algebra to get translations from
  one language to another and prove the correctness of the compilation
  by relating semantics of the source and target languages. As far as
  we know, this is the first formalization in type-theory of the
  concept of \emph{derived signature morphism}.
\end{abstract}

\category{CR-number}{subcategory}{third-level}

% general terms are not compulsory anymore,
% you may leave them out
\terms
term1, term2

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
