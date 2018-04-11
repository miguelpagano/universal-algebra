\documentclass{entcs} \usepackage{entcsmacro}

\sloppy
% The following is enclosed to allow easy detection of differences in
% ascii coding.
% Upper-case    A B C D E F G H I J K L M N O P Q R S T U V W X Y Z
% Lower-case    a b c d e f g h i j k l m n o p q r s t u v w x y z
% Digits        0 1 2 3 4 5 6 7 8 9
% Exclamation   !           Double quote "          Hash (number) #
% Dollar        $           Percent      %          Ampersand     &
% Acute accent  '           Left paren   (          Right paren   )
% Asterisk      *           Plus         +          Comma         ,
% Minus         -           Point        .          Solidus       /
% Colon         :           Semicolon    ;          Less than     <
% Equals        =3D           Greater than >          Question mark ?
% At            @           Left bracket [          Backslash     \
% Right bracket ]           Circumflex   ^          Underscore    _
% Grave accent  `           Left brace   {          Vertical bar  |
% Right brace   }           Tilde        ~

\def\lastname{Gunther, Gadea, and Pagano}

\usepackage{amsmath}
\usepackage{bussproofs}
\usepackage{ upgreek }
\usepackage[inline]{enumitem}
\usepackage{calc}
\newcounter{descriptcount}
\renewcommand*\thedescriptcount{\arabic{descriptcount}}
\newcommand{\setoidMor}{{\xrightarrow{\,\thickapprox\,}}}
%format VecH' = HVec
%format 〉 = ")"
%format 〈 = "("
%format ⟨⟨ = "\langle\!"
%format ⟩⟩ = "\!\rangle"
%format ⟶ = "\ensuremath{\setoidMor}"
%format _⟶_ = "\ensuremath{\_\setoidMor\_}"
%format _≈→_ = "\ensuremath{\_\mathop{≈_{\mathit{ext}}}\_}"
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
%format |Tc| = "T_m"
%format ∣h∣→A = |h|
%format ∣h*∣→A = |h*|
%format map|h|→A = map|h|
%format |h|A = |H|
%format |h'|A = H
%format _⊨Σ_ = "\Varid{\char95}\ensuremath{\models_{\Sigma}}\Varid{\char95}"
%% "\ensuremath{h_{A}}"
%% "\ensuremath{h_{A}^{\ast}}"

%include agda.fmt
%include unicode.fmt
\DeclareUnicodeCharacter{7504}{\ensuremath{^{m}}}
\DeclareUnicodeCharacter{10140}{\ensuremath{\Rightarrow}}
\DeclareUnicodeCharacter{10035}{\ensuremath{\ast}}
\DeclareUnicodeCharacter{8338}{\ensuremath{_{o}}}
\DeclareUnicodeCharacter{7525}{\ensuremath{_{v}}}
\DeclareUnicodeCharacter{7506}{\ensuremath{^{o}}}
\DeclareUnicodeCharacter{8407}{\ensuremath{^{\rightarrow}}}
\DeclareUnicodeCharacter{12296}{(}
\DeclareUnicodeCharacter{12297}{)}
\newcommand{\cL}{{\cal L}}
\newcommand{\ie}{i.e.\@@ }
\newcommand{\manu}[1]{} % \textcolor{red}{#1}}
\renewcommand{\alg}[1]{\mathcal{#1}}
\newcommand{\iso}{\equiv}
\newcommand{\comment}[1]{}
\newlength{\abdisplay}
\newlength{\bldisplay}

% Uncomment the publication rights you want to use.
%\publicationrights{transferred}
%\publicationrights{licensed}     % this is the default
%\publicationrights{author-pays}

\newcommand{\mailto}[1]{\href{mailto:#1}{{\texttt{\normalshape #1}}}}
\begin{document}
\begin{frontmatter}
\title{Formalization of Universal Algebra in Agda}
\author{Emmanuel Gunther
\thanksref{manumail}}
  \author{Alejandro Gadea\thanksref{alemail}}
  \author{Miguel Pagano\thanksref{miguelmail}}
  \address{FaMAF, UNC -- C\'{o}rdoba, Argentina }
 \thanks[manumail]{Email:\mailto{gunther@@famaf.unc.edu.ar} Partially supported by a CONICET scholarship.}
 \thanks[alemail]{Email:\mailto{gadea@@famaf.unc.edu.ar} Partially supported by a CONICET scholarship.}
 \thanks[miguelmail]{Email:\mailto{pagano@@famaf.unc.edu.ar}}

\begin{abstract}
In this work we present a novel formalization of
universal algebra in Agda. We show that heterogeneous signatures can
be elegantly modelled in type-theory using sets indexed by arities to
represent operations. We prove elementary results of heterogeneous
algebras, including the proof that the term algebra is initial and the
proofs of the three isomorphism theorems. We further formalize equational theory and
prove soundness and completeness. At the end, we define (derived)
signature morphisms, from which we get the contra-variant functor
between algebras; moreover, we also proved that, under some
restrictions, the translation of a theory induces a contra-variant
functor between models.
\end{abstract}
\begin{keyword}
universal algebra, formalization of mathematics, equational logic
\end{keyword}
\end{frontmatter}

\setlength{\abdisplay}{\abovedisplayskip - 1pt}
\setlength{\bldisplay}{\belowdisplayskip - 1pt}

%include introduction.lagda
%include univ-alg.lagda
%include equational.lagda
%include transforming-algebras.lagda
%include conclusions.lagda
\bibliographystyle{entcs}
\bibliography{biblio}
\end{document}
