\documentclass[acmsmall,screen,review]{acmart}

\settopmatter{printccs=false, printacmref=false}
\setcopyright{none}

\acmJournal{PACMPL}
\acmVolume{0}
\acmNumber{0}
\acmArticle{0}
%\acmMonth{9}

%\ifPDFTeX
%\usepackage[T1]{fontenc}
%\usepackage[utf8]{inputenc}
%\usepackage[british]{babel}
%\else
%\usepackage{polyglossia}
%\setdefaultlanguage{british}
%\fi

\usepackage[capitalise,noabbrev]{cleveref}

\usepackage{mathtools}

\usepackage{listings}
\lstset{language=Haskell, basicstyle=\ttfamily, basewidth=0.5em, xleftmargin=2\parindent}

\usepackage{mdframed}

\usepackage{xifthen}
\newcommand{\varcitet}[3][]{\citeauthor{#2}#3~[\ifthenelse{\isempty{#1}}{\citeyear{#2}}{\citeyear[#1]{#2}}]}

\usepackage[inline]{enumitem} % for environment enumerate*

\setlength{\marginparwidth}{1.25cm}
\usepackage[obeyFinal,color=yellow,textsize=scriptsize]{todonotes}

\let\Bbbk\relax
%include agda.fmt

%format →' = "\kern-.345em\mathrlap{\to}"
%format ∘ = "{\cdot}"

%format tipₙ = tip "_{\Conid n}"

\newcommand{\Var}[1]{\mathit{#1}}

%format A = "\Var A"
%format P = "\Var P"

%format n = "\Var n"
%format k = "\Var k"
%format x = "\Var x"
%format xs = "\Var xs"
%format ys = "\Var ys"

\begin{document}

\setlength{\mathindent}{2\parindent}

\author{Hsiang-Shang Ko}
\email{joshko@@iis.sinica.edu.tw}
\orcid{0000-0002-2439-1048}
\author{Shin-Cheng Mu}
\email{scm@@iis.sinica.edu.tw}
\orcid{0000-0002-4755-601X}
\affiliation{%
  \institution{Academia Sinica}
  \streetaddress{128 Academia Road}
  \city{Taipei}
  \country{Taiwan}
  \postcode{115201}
}
\author{Jeremy Gibbons}
\email{jeremy.gibbons@@cs.ox.ac.uk}
\orcid{0000-0002-8426-9917}
\affiliation{%
  \institution{University of Oxford}
  \streetaddress{Wolfson Building, Parks Road}
  \city{Oxford}
  \country{UK}
  \postcode{OX1 3QD}
}

\title{Binomial Tabulation: A Short Story (Functional Pearl)}

\begin{abstract}
\end{abstract}

%\begin{CCSXML}
%<ccs2012>
%   <concept>
%       <concept_id>10011007.10011006.10011041</concept_id>
%       <concept_desc>Software and its engineering~Compilers</concept_desc>
%       <concept_significance>500</concept_significance>
%       </concept>
%   <concept>
%       <concept_id>10011007.10011006.10011039.10011040</concept_id>
%       <concept_desc>Software and its engineering~Syntax</concept_desc>
%       <concept_significance>500</concept_significance>
%       </concept>
%   <concept>
%       <concept_id>10011007.10011074.10011099.10011692</concept_id>
%       <concept_desc>Software and its engineering~Formal software verification</concept_desc>
%       <concept_significance>300</concept_significance>
%       </concept>
%   <concept>
%       <concept_id>10003752.10003790.10011740</concept_id>
%       <concept_desc>Theory of computation~Type theory</concept_desc>
%       <concept_significance>500</concept_significance>
%       </concept>
% </ccs2012>
%\end{CCSXML}
%
%\ccsdesc[500]{Software and its engineering~Compilers}
%\ccsdesc[500]{Software and its engineering~Syntax}
%\ccsdesc[300]{Software and its engineering~Formal software verification}
%\ccsdesc[300]{Theory of computation~Type theory}
%
%\keywords{datatype-generic programming, language formalisation, \Agda}

\maketitle

`What on earth is this function doing?'

I stared at the late Richard Bird's `Zippy Tabulations of Recursive Functions'~\citeyearpar{Bird-zippy-tabulations}, frowning.

\begin{lstlisting}
cd                        :: B a -> B (L a)
cd (Bin (Tip a) (Tip b))  =  Tip [a, b]
cd (Bin u (Tip b))        =  Bin (cd u) (B (: [b]) u)
cd (Bin (Tip a) v)        =  Tip (a : as) where Tip as = cd v
cd (Bin u v)              =  Bin (cd u) (zipBWith (:) u (cd v))
\end{lstlisting}

I knew \lstinline{B} was this datatype of trees
\begin{lstlisting}
data B a = Tip a || Bin (B a) (B a)
\end{lstlisting}
and \lstinline{L} was the usual list datatype, but how did Richard come up with such a complicated function definition?
And he didn't bother to explain it in the paper.

\todo[inline]{Monologue of a dependently typed programmer, highlighting what they think about (in an intuitive and colloquial style) when solving the problem/mystery (cf~the beginning of the science fiction novel \textit{Project Hail Mary})}

\begin{mdframed}[backgroundcolor=red!7, linewidth=0, skipabove=1ex, leftmargin=1ex, rightmargin=0, innerleftmargin=0, innerrightmargin=0, innertopmargin=0, innerbottommargin=0]
\begin{code}
data BT (A : Set) : ℕ → ℕ → Set where
  tip₀  :   A                → BT A       n     0
  tipₙ  :   A                → BT A (1 +  n) (  1 + n)
  bin   :   BT A n (1 +  k)
        →'  BT A n       k   → BT A (1 +  n) (  1 + k)
\end{code}
\end{mdframed}

\begin{code}
data BT : (n k : ℕ) → (Vec A k → Set) → Vec A n → Set where
  tip₀  :   P []                             → BT       n     0       P xs
  tipₙ  :   P xs                             → BT (1 +  n) (  1 + n)  P xs
  bin   :   BT n (1 +  k)   P            xs
        →'  BT n       k (  P ∘ (x ∷_))  xs  → BT (1 + n) (1 + k) P (x ∷ xs)
\end{code}

\bibliographystyle{ACM-Reference-Format}
\bibliography{bib}

\end{document}
