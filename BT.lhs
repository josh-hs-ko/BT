%let anonymous = True

\documentclass[%
%if anonymous
anonymous,
%endif
acmsmall,fleqn,screen,review]{acmart}

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
\citestyle{acmauthoryear}
\crefformat{equation}{(#2#1#3)}

\usepackage{mathtools}
\usepackage{varwidth}
\usepackage{pifont}

\usepackage{listings}
\lstset{basicstyle=\ttfamily, basewidth=0.5em, xleftmargin=2\parindent, morekeywords={data, where}}

\usepackage{mdframed}
\newenvironment{temp}{\begin{mdframed}[backgroundcolor=red!7, linewidth=0, skipabove=1ex, leftmargin=1ex, rightmargin=0, innerleftmargin=0, innerrightmargin=0, innertopmargin=0, innerbottommargin=0]\setlength{\abovedisplayskip}{0ex}\raisebox{-\height-3pt}[0pt][0pt]{\hspace{.965\textwidth}\color{red}\huge\ding{56}}}{\end{mdframed}}
%\definecolor{SkyBlue}{HTML}{D9F6FF}
%\newenvironment{final}{\begin{mdframed}[backgroundcolor=SkyBlue, linewidth=0, skipabove=1ex, leftmargin=1ex, rightmargin=0, innerleftmargin=0, innerrightmargin=0, innertopmargin=0, innerbottommargin=0]}{\end{mdframed}}

\usepackage{xifthen}
\newcommand{\varcitet}[3][]{\citeauthor{#2}#3~[\ifthenelse{\isempty{#1}}{\citeyear{#2}}{\citeyear[#1]{#2}}]}

\usepackage[inline]{enumitem} % for environment enumerate*
\newlist{inlineenum}{enumerate*}{1}
\setlist[inlineenum]{label=(\arabic*)}

\setlength{\marginparwidth}{1.25cm}
\usepackage[obeyFinal,color=yellow,textsize=scriptsize]{todonotes}

\newcommand{\Josh}[1]{\footnote{\color{blue}Josh: #1}}
\newcommand{\Shin}[1]{\footnote{\color{blue}Shin: #1}}
\newcommand{\Jeremy}[1]{\footnote{\color{blue}Jeremy: #1}}

\newenvironment{aha}{\medskip}{\medskip} % for one-line paragraphs
\newcommand{\pause}{\medskip\centerline{$\ast\quad\ast\quad\ast$}\medskip} % for a mid-section pause

\newcommand{\csp}{\hspace{.5em}}
\newcommand{\equals}{\enskip=\enskip}

\usepackage{tikzit}
\input{string.tikzstyles}

\let\Bbbk\relax
%include agda.fmt

\definecolor{suppressed}{RGB}{225,225,225}
\definecolor{goal}{RGB}{209,243,205}
\newcommand{\highlight}[2]{\smash{\text{\colorbox{#1}{\kern-.1em\vphantom{\vrule height 1.35ex depth 0.16ex}\smash{\ensuremath{#2}}\kern-.1em}}}}

%format (SUPPRESSED(t)) = "\highlight{suppressed}{" t "}"
%format (GOAL(t)(i)) = "\highlight{goal}{\textbf\{\," t "\,\textbf\}_{\kern1pt" i "}}"
%format G0 = "\textbf{0}"
%format G1 = "\textbf{1}"
%format G2 = "\textbf{2}"
%format G3 = "\textbf{3}"
%format G4 = "\textbf{4}"
%format G5 = "\textbf{5}"
%format G6 = "\textbf{6}"
%format G7 = "\textbf{7}"
%format G8 = "\textbf{8}"
%format G9 = "\textbf{9}"
%format G10 = "\textbf{10}"
%format G11 = "\textbf{11}"
%format ?0 = "\mathrm{?_0}"
%format ?1 = "\mathrm{?_1}"
%format ?2 = "\mathrm{?_2}"
%format ?3 = "\mathrm{?_3}"
%format ?4 = "\mathrm{?_4}"
%format ?5 = "\mathrm{?_5}"
%format ?6 = "\mathrm{?_6}"
%format ?7 = "\mathrm{?_7}"
%format ?8 = "\mathrm{?_8}"
%format ?9 = "\mathrm{?_9}"
%format ?10 = "\mathrm{?_{10}}"
%format ?11 = "\mathrm{?_{11}}"

\newcommand{\ignorenext}[1]{}

%format (sub(x)) = "\unskip_{" x "}"
%format (C(n)(k)) = "\unskip^{" n "}_{" k "}"
%format (CHOOSE (n) (k)) = "C{}^{" n "}_{" k "}"

%format @ = "\unskip@\ignorenext"
%format =' = "\unskip=\ignorenext"
%format →' = "\kern-.345em\mathrlap{\to}"
%format ↝ = "\unskip\leadsto\ignorenext"
%format ⇉ = "\unskip\rightrightarrows\ignorenext"
%format ⇉' = "{\rightrightarrows}"
%format _⇉_ = _ "{\rightrightarrows}" _
%format ∘ = "\unskip\mathrel\cdot\ignorenext"
%format _∘_ = _ "\kern1pt{\cdot}\kern.5pt" _
%format ⊗ = "\unskip\otimes\ignorenext"
%format ≡ = "\unskip\equiv\ignorenext"
%format ∈ = "\unskip\in\ignorenext"
%format [ = "[\kern-2pt"
%format ] = "\kern-2pt]"
%format Σ[ = Σ [
%format ∀[ = ∀ [
%format _∷_ = _ "\kern.5pt" ∷ _
%format ∷_ = ∷ _
%format _∷ = _ "\kern.5pt" ∷
%format ᴮᵀ = "_{\Conid{BT}}"
%format ∷ᴮᵀ = ∷ ᴮᵀ
%format _∷ᴮᵀ_ = _ "\kern.5pt" ∷ᴮᵀ _
%format _∷ᴮᵀ = _ "\kern.5pt" ∷ᴮᵀ
%format > = "\unskip>\ignorenext"
%format GEQ = "\unskip\ge\ignorenext"
%format ≤ = "\unskip\le\ignorenext"
%format < = "\unskip<\ignorenext"
%format ≤↑ = "\unskip\mathrel{\le_\uparrow}\ignorenext"
%format _≤↑_ = _ "\kern.5pt{\le_\uparrow}" _
%format ↓≤ = "\unskip\mathrel{_\downarrow\kern-.8pt{\le}}\ignorenext"
%format _↓≤_ = _ "\kern.5pt{_\downarrow\kern-.8pt{\le}}" _
%format ↓≤' = "{_\downarrow\kern-.8pt{\le}}"
%format CDOTS = "\cdots"

%format B' = B "^\prime"
%format (B'_(n)(k)) = B' "{}^{" n "}_{" k "}"
%format testB' = test B'
%format (BT_(n)(k)) = BT "^{" n "}_{" k "}"
%format mapBT = map ᴮᵀ
%format zipBTWith = zip ᴮᵀ "\kern-1pt" With
%format Fun = "\text{\textbf{\textsf{Fun}}}"
%format Fam' = "\text{\textbf{\textsf{Fam}}}"
%format mapExactly = map "_{" Exactly "}"

%format 0 = "\mathrm 0"
%format 1 = "\mathrm 1"
%format 2 = "\mathrm 2"
%format 3 = "\mathrm 3"

\newcommand{\Con}[1]{\mathbf{#1}}

%format bin = "\Con{bin}"
%format exactly = "\Con{exactly}"
%format refl = "\Con{refl}"
%format base = "\Con{base}"
%format step = "\Con{step}"
%format suc = "\Con{suc}"
%format tipZ = "\Con{tip_z}"
%format tipS = "\Con{tip_s}"
%format tt = "\Con{tt}"
%format zero = "\Con{zero}"

\newcommand{\Var}[1]{\mathit{#1}}

%format D = "\Var D"
%format F = "\Var F"
%format F' = "\Var F^\prime"
%format G = "\Var G"
%format G' = "\Var G^\prime"
%format H = "\Var H"
%format K = "\Var K"
%format a = "\Var a"
%format b = "\Var b"
%format c = "\Var c"
%format d = "\Var d"
%format e = "\Var e"
%format f = "\Var f"
%format f' = "\Var f^\prime"
%format g = "\Var g"
%format h = "\Var h"
%format i = "\Var i"
%format k = "\Var k"
%format m = "\Var m"
%format n = "\Var n"
%format p = "\Var p"
%format param = "\Var{param}"
%format pz = "\Var{pz}"
%format ps = "\Var{ps}"
%format q = "\Var q"
%format qz = "\Var{qz}"
%format qs = "\Var{qs}"
%format r = "\Var r"
%format s = "\Var s"
%format t = "\Var t"
%format u = "\Var u"
%format v = "\Var v"
%format ws = "\Var ws"
%format x = "\Var x"
%format x₁ = "{\Var x}_{1}"
%format xs = "\Var xs"
%format y = "\Var y"
%format ys = "\Var ys"
%format z = "\Var z"
%format zs = "\Var zs"
%format α = "\alpha"
%format α' = "\alpha^\prime"
%format β = "\beta"
%format γ = "\gamma"
%format δ = "\delta"

%format sn = 1 + n
%format ssn = 2 + n
%format sssn = 3 + n
%format sk = 1 + k
%format ssk = 2 + k
%format sssk = 3 + k

%format n>k = n "{>}" k
%format nGEQk = n "{\geq}" k
%format skGEQk = sk "{\geq}" k
%format nGEQsk = n "{\geq}" sk

%format BLANK = "~~"

\begin{document}

\setlength{\mathindent}{2\parindent}

\author{Hsiang-Shang Ko}
\email{joshko@@iis.sinica.edu.tw}
\orcid{0000-0002-2439-1048}
\author{Shin-Cheng Mu}
\email{scm@@iis.sinica.edu.tw}
\orcid{0000-0002-4755-601X}
\affiliation{
  \institution{Academia Sinica}
  \department{Institute of Information Science}
  \streetaddress{128 Academia Road}
  \city{Taipei}
  \country{Taiwan}
  \postcode{115201}
}
\author{Jeremy Gibbons}
\email{jeremy.gibbons@@cs.ox.ac.uk}
\orcid{0000-0002-8426-9917}
\affiliation{
  \institution{University of Oxford}
  \department{Department of Computer Science}
  \streetaddress{Wolfson Building, Parks Road}
  \city{Oxford}
  \country{UK}
  \postcode{OX1 3QD}
}

\title{Binomial Tabulation: A Short Story (Functional Pearl)}

\begin{abstract}
\todo[inline]{Abstract: a demonstration of dependent types and string diagrams for the functional programmer (ideally already with a bit exposure to dependent types and category theory and not put off by basic concepts like indexed types, functors, and so on); an outline of the paper
\vspace{10\baselineskip}}
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

%\todo[inline]{Proposal of `chapter' headings (replacing the current sections): `Simple Types' for (the original) S1 \& S2, `Dependent Types' for S3 \& S4, and `String Diagrams' for S5 \& S6, which are the languages used in the chapters. JG: how about `Functions', `Types', `Diagrams'? or `Functional Programming', `Dependent Types', `Category Theory'? I think we \emph{do} need subsections now; \S2 is a rather indigestible 10pp lump. Josh: Added some subsections.}

%\tableofcontents

\section{Functions}
\label{sec:functions}

`What on earth is this function doing?'

I stare at the late Richard Bird's~\citeyearpar{Bird-zippy-tabulations} paper `Zippy Tabulations of Recursive Functions', frowning.

\begin{lstlisting}
cd :: B a -> B (L a)
cd (Bin (Tip y) (Tip z)) = Tip [y,z]
cd (Bin (Tip y) u      ) = Tip (y : ys) where Tip ys = cd u
cd (Bin t       (Tip z)) = Bin (cd t) (mapB (: [z]) t)
cd (Bin t       u      ) = Bin (cd t) (zipBWith (:) t (cd u))
\end{lstlisting}

I know \lstinline{B} is this Haskell data type of binary trees:
\begin{lstlisting}
data B a = Tip a || Bin (B a) (B a)
\end{lstlisting}
And presumably \lstinline{mapB} and \lstinline{zipBWith} are the usual \lstinline{map} and \lstinline{zipWith} functions for these trees, and \lstinline{L} is the standard data type of lists.
But how did Richard come up with such an incomprehensible function definition?
%\Jeremy{We should be more consistent about whether to call him Richard or Bird. Shin: does it work if we say "Richard" when we refer to the person and say Bird (2008) when we refer to the paper?}
He didn't bother to explain it in the paper.
%\Jeremy{Such contractions are fine, when ``in character''.}

\subsection{Top-Down and Bottom-Up Algorithms}
\label{sec:algorithms}

From the explanations that \emph{are} in the paper, I can make a pretty good guess at roughly what \lstinline{cd} should do.
Richard was studying the relationship between top-down and bottom-up algorithms that solve problems specified recursively on some input data structure.
When the input is a non-empty list, a generic top-down algorithm is defined by
%\todo{Make the function polymorphic}
%\Josh{Include |f| and |g| as arguments (like |foldr| etc). Shin: Done.}
%\Jeremy{Can we avoid using \lstinline{$}? Richard wouldn't have used it\ldots. Shin: Used application instead.}
\begin{lstlisting}
td :: (a -> s) -> (L s -> s) -> L a -> s
td f g [x] = f x
td f g xs  = g (map (td f g) (dc xs))
\end{lstlisting}
The input of \lstinline{td} is a non-empty list of \lstinline{a}'s, and the output is a solution of type \lstinline{s} for the list.
Singleton lists form the base cases, for which a solution is directly computed by a given function~\lstinline{f}.
If a non-empty list \lstinline{xs} is non-singleton, it is decomposed into shorter lists by some\csp\lstinline{dc :: L a -> L (L a)}.
Then a subsolution is computed for each shorter list recursively by \lstinline{td}.
Finally, \lstinline{g}~combines the subsolutions into a solution for \lstinline{xs}.
In fact, in order to cover a wider range of algorithms, Richard's definition is more abstract and general.
%\lstinline{L}~needs not be a list, and \lstinline{dc} returns an \lstinline{F}-structure of lists.
But I'm working with this simplified version as an easier starting point.
%\Shin{Hope this is sufficient and yet not too verbose.}
%\Josh{\lstinline{F} is initially \lstinline{L} and later \lstinline{B}, but this changes the type of \lstinline{g} too (no need for \lstinline{cvt} etc)? Shin: removed \lstinline{F}. I think we still need \lstinline{cvt} after switching to \lstinline{B}.}
%\Shin{We need to somehow mention that ``The setting in \citet{Bird-zippy-tabulations} is more general: \lstinline{L} need not be a list, and \lstinline{dc} returns an \lstinline{F}-structure of lists. We simplified the setting for ease of discussion'' without being out-of-character.}

\begin{figure}[t]
\centering
\includegraphics[width=0.95\textwidth]{pics/td-call-tree.pdf}
\caption{Computing\csp\lstinline{td "abcd"}\csp top-down.}
\label{fig:td-call-tree}
\end{figure}

In the last (and the most difficult) example in the paper, \lstinline{dc} computes all the \emph{immediate sublists} of the given list --- all the lists with exactly one element missing:
%\Josh{Inline monospace code with spaces will need space corrections before and after.}
\begin{lstlisting}
dc :: L a -> L (L a)
dc [x,y]       = [[x],[y]]
dc (xs ++ [x]) = [xs] ++ [ys ++ [x] || ys <- dc xs]
\end{lstlisting}
(Richard assumed that a list could be matched with a snoc pattern\csp\lstinline{xs ++ [x]}.)
For example, computing a solution for \lstinline{"abcd"} requires subsolutions for \lstinline{"abc"},\lstinline{"abd"}, \lstinline{"acd"}, and \lstinline{"bcd"}~(\cref{fig:td-call-tree}).
In turn, computing a solution for \lstinline{"abc"} requires subsolutions for \lstinline{"ab"}, \lstinline{"ac"}, and \lstinline{"bc"}, and so on.
When the problem decomposition reaches length-$2$ sublists ---~that's a bit of a mouthful, so let me just say `$2$-sublists' for short~--- it becomes evident that this \lstinline{dc} leads to \emph{overlapping subproblems}, and \lstinline{td} deals with that very inefficiently.
For example, a solution for \lstinline{"ab"} is required for solving the problem for \lstinline{"abc"} and \lstinline{"abd"}, and \lstinline{td} computes that solution twice.
And it gets worse further down: a solution for each $1$-sublist is computed $6$~times!
%\Josh{We probably have space for the entire call tree. And how about making all the \lstinline{td}s in all the figures slightly transparent and less obtrusive? SCM: Tried to fit them all in, and used grey for \lstinline{td}.}

\begin{figure}[t]
\centering
\includegraphics[width=0.75\textwidth]{pics/sublists-lattice.pdf}
\caption{Computing\csp\lstinline{td "abcd"}\csp bottom-up.}
\label{fig:sublists-lattice}
\end{figure}

It's better to proceed bottom-up instead, working upwards through a lattice of sublists~(\cref{fig:sublists-lattice}), level by level.
Level~$1$ consists of solutions for the $1$-sublists.
Then solutions for the $(k+1)$-sublists in level $k+1$ are computed from subsolutions in level~$k$.
Finally, the top level consists of a single solution, for the input list.
More specifically, if the levels were represented as lists, level~$2$ would be
\begin{lstlisting}
[td "ab", td "ac", td "bc", td "ad" ...]
\end{lstlisting}
One way to construct level~$3$ from level~$2$ would be using a function\csp\lstinline{cd' :: L a -> L (L a)}\csp that copies and rearranges the elements such that the subsolutions for the immediate sublists of the same list are brought together:
\begin{lstlisting}
[[td "ab", td "ac", td "bc"], [td "ab", td "ad", td "bd"] ...]
\end{lstlisting}
Then applying\csp\lstinline{map g}\csp to this list of lists would produce level~$3$:
\begin{lstlisting}
[td "abc", td "abd", td "acd", td "bcd" ...]
\end{lstlisting}
If such a function \lstinline{cd'} could be constructed, a bottom-up algorithm computing the same solution as \lstinline{td} would be given by
%\Josh{Bring \lstinline{head} in front of \lstinline{loop}? Shin: Done.}
%\Jeremy{Unless we're really pressed for space, I think it is better to put this on four lines. Shin: Done.}
\begin{lstlisting}
bu' :: (a -> s) -> (L s -> s) -> L a -> s
bu' f g = head . loop . map f
  where
    loop [y] = [y]
    loop ys  = loop (map g (cd ys))
\end{lstlisting}
Level~$1$ is obtained by applying \lstinline{f} to each element of the input list.
Then the \lstinline{loop} function keeps applying\csp\lstinline{map g . cd'}\csp to get the next level.
It stops at a level with a single element, which is a solution for the input list.
Like \lstinline{td}, this \lstinline{bu'} is a simplified version.
To cope with more general problems, Richard had to store something more complex in each level, but I don't think I need that.
%\Jeremy{``\ldots next level. We stop when\ldots''---and generally, shorter sentences is punchier, and more plausible as direct speech/thought.}

\subsection{Binary Trees}
\label{sec:bu}

That's what I understand about \lstinline{cd} so far.
But Richard must have realised at some point that it's difficult to define the \lstinline{cd} rearrangement using lists, and decided to represent each level using the \lstinline{B}~data type.
So\csp\lstinline{cd :: B a -> B (L a)}, and the (real) bottom-up algorithm \lstinline{bu} is defined by
\begin{lstlisting}
bu :: (a -> s) -> (L s -> s) -> L a -> s
bu f g = unTip . loop . cvt . map f
  where
    loop (Tip x) = Tip x
    loop xs      = loop (mapB g (cd xs))
\end{lstlisting}
where \lstinline{unTip} extracts the element of a \lstinline{Tip} tree,
\begin{lstlisting}
unTip :: B a -> a
unTip (Tip x) = x
\end{lstlisting}
and \lstinline{cvt} converts a list to a tree:
\begin{lstlisting}
cvt :: L a -> B a
cvt [x]         = Tip x
cvt (xs ++ [x]) = Bin (cvt xs) (Tip x)
\end{lstlisting}

I wonder if I have to use~\lstinline{B} instead of lists in \lstinline{cd}.
If I'm given level~1 of the lattice~(\cref{fig:sublists-lattice}) as a 4-list, I know they are solutions for the four 1-sublists, and surely there's no problem rearranging them into level~2\ldots?

Oh wait, I don't actually know.
All I get is a 4-list.
This 4-list could be level~1, but it could well be level~3.
And I don't get any information from the elements --- the element type is parametrically quantified.
So there isn't enough context for me to decide whether I should produce a 6-list (level~2) or a 1-list (level~4).

\begin{figure}[t]
\centering
\includegraphics[width=0.8\textwidth]{pics/map_g_cd.pdf}
\caption{How\csp\lstinline{mapB g . cd}\csp constructs a new level.}
\label{fig:map_g_cd}
\end{figure}

Presumably, Richard's trees gave him more context.
I try to trace Richard's \lstinline{cd} to find out how it works.
Given input \lstinline{"abcd"}, the function\csp\lstinline{cvt . map f}\csp yields a tree slanted to the left as level~$1$:
%\Josh{Wrong order? Shin: Richard's \lstinline{cvt} is \lstinline{foldl1 Bin . map Tip}.. so it is his order. If that's not consistent with ours... let's think about what to do. :(}
\begin{lstlisting}
Bin (Bin (Bin (Tip (td "a")) (Tip (td "b"))) (Tip (td "c"))) (Tip (td "d"))
\end{lstlisting}
Following Richard's convention, I draw a\csp\lstinline{Tip x}\csp as \lstinline{x}, and\csp\lstinline{Bin t u}\csp as a dot with~\lstinline{t} to its left and \lstinline{u}~below~(\cref{fig:map_g_cd}).
%\Josh{(Caption of \cref{fig:map_g_cd}) `Note that to save space we omit \lstinline{td}, thus \lstinline{ab}, \lstinline{ac}... etc. denote results of \lstinline{td}, not the sublists themselves.' We have space now. SCM: Put \lstinline{td}s back.}
Applying\csp\lstinline{mapB g . cd}\csp to this, I get level~$2$. % labelled (2) in the figure.
For a closer look, I apply only \lstinline{cd} to level~$2$.
Indeed, with its clever mapping and zipping, \lstinline{cd} manages to bring together precisely the right elements, and produces a `level~$2{}^{1\kern-.2em}/_{\!2}$'. % `level~$2.5$'.
Then I reach level~$3$ by applying\csp\lstinline{mapB g}.
There's indeed more context for distinguishing levels $1$~and~$3$: their tree representations have different shapes.

The intuition about having enough context seems useful.
I was puzzled by why Richard started from singleton lists instead of the empty list.
The intuition helps to explain that too.
Level~$0$ would be a singleton list/tree, and I wouldn't know the number of values level~$1$ should contain.
That number is the length of the input list, and \lstinline{cd} doesn't get that information.
So there isn't enough context for going from level~$0$ to level~$1$, regardless of how levels are represented.

%\Shin{I added the second sentence in the caption of Figure~\ref{fig:map_g_cd}. I think it's probably necessary because I myself got confused from time to time.
%Josh: This might be related to the question about the role of~|p| in |BT|.}
%\Josh{Should update this paragraph and \cref{fig:map_g_cd} for just \lstinline{"abcd"}.
%SCM: But I think we need an input with 5 elements to see more structure in the tree. I'd rather update previous examples to \lstinline{"abcde"} if we have to...
%It's probably too much to use \lstinline{"abcde"} in S3, however.
%Josh: We don't see that the numbers are related to binomial coefficients ourselves --- Richard told us. So I'd say seeing more of the numbers is not more important than consistency. Ultimately the question may be: what's the necessary information in this example for figuring out the indexing of~|B|? I suspect five elements are not more useful than four.
%SCM: changed the picture.}

%\todo[inline]{`A $2$-list is completely determined by its two $1$-sublists, but a $1$-list is not determined by its one $0$-sublist --- more context would be needed. All these, however, are merely a first attempt.
%Richard must have realised at some point that it is difficult to define the \lstinline{cd} rearrangement using lists, and decided to represent each level using the \lstinline{B}~data type.'
%This explanation doesn't seem directly related to \lstinline{cd}?
%Rather, representing levels as lists doesn't provide enough context for \lstinline{cd} to do its job --- for example, a $6$-list can represent level~$2$ in a $4$-lattice or level~$1$ in a $6$-lattice.
%Partly justifying Richard's decision to use \lstinline{B} instead --- the two levels with $6$~elements have different shapes as trees.}

\subsection{Binomial Trees}
\label{sec:binomial}

That still doesn't give me much insight into why \lstinline{cd} works though.
Presumably, \lstinline{cd} does something useful only for the trees built by\csp\lstinline{cvt . map f}\csp and \lstinline{cd} itself.
What are the constraints on these trees, and how does \lstinline{cd} exploit them?
%\Josh{To be explicitly responded at the end of S3}

Richard did give a hint: the sizes of subtrees along their left spines (the red numbers in Figure~\ref{fig:map_g_cd}) $[1,2,3,4]$, $[1,3,6]$, and $[1,4]$ are the first three diagonals of Pascal's triangle --- the trees are related to binomial coefficients!
%So the name \lstinline{B} refers to `binomial' in addition to `binary'.
The binomial coefficient~|CHOOSE n k| is the number of ways of choosing $k$~elements from an $n$-list.
Indeed, each level~$k$ in the lattice~(\cref{fig:sublists-lattice}) contains values about $k$-sublists.
For example, level~$2$ has |CHOOSE 4 2 =' 6| values --- there are $6$~ways of choosing $2$~elements from a $4$-list.

Aha!
I can even see a pattern related to element choosing in the tree representation of level~$2$~(\cref{fig:map_g_cd}): the right subtree is about all the 2-sublists that end with~\lstinline{'d'}, and the left subtree about the other 2-sublists not containing~\lstinline{'d'}.
To choose $2$~elements from \lstinline{"abcd"}, I can include the rightmost element~\lstinline{'d'} or not.
If \lstinline{'d'}~is included, there are |CHOOSE 3 1| ways of choosing $1$~element from \lstinline{"abc"} to go with~\lstinline{'d'}.
If \lstinline{'d'}~is not included, there are |CHOOSE 3 2| ways of choosing $2$~elements from \lstinline{"abc"}.
And the total number of $2$-sublists is |(CHOOSE 3 2) + (CHOOSE 3 1) =' (CHOOSE 4 2)|.
All the \lstinline{Bin} nodes fit this pattern.
I guess the trees are supposed to satisfy a binomial shape constraint (and the name of the~\lstinline{B} data type could refer to `binomial' in addition to `binary').

That's about as many clues as I can get from Richard's paper for now.
Given these clues, how do I prove that \lstinline{cd} indeed does the job --- bringing values about related immediate sublists together?
In fact, how do I even write that down as a formal specification?
And how does that help me to prove that \lstinline{td} equals \lstinline{bu}?
%\Josh{and proving \lstinline{td} equals \lstinline{bu}. Shin: added.}

I'm worried that there will be many complex proofs waiting ahead for me.

%\todo[inline]{Recap of what Richard's paper wanted to do: transforming a top-down algorithm (which acts as a specification) to a bottom-up algorithm, which `I' (Shin) had already worked out a simplified version; explain why the base cases have to be singleton lists; the role of \lstinline{cd} in the bottom-up algorithm, intuitively; relationship to binomial cofficients}

%But I still couldn’t see, \emph{formally}, how to make sense of the definition of \lstinline{cd} or get from the definition to a correctness proof of \lstinline{bu}.
%\todo{Main question; even suggest there's a lot of proving ahead (actually not)}

\section{Types}

\subsection{Shapes in Types}
\label{sec:shape}

The binomial shape constraint seems to be the easiest next target, because there's a standard solution: capturing the tree shape in its type.
Shape-indexed data types are so common now that I'm tempted to say they should count as simple types.
They are common even in Haskell.
I prefer a proper dependently typed language though, so I open my favourite editor, and switch to Agda.

The classic example of shape-indexing is, of course, length-indexed lists (or `vectors'):
\begin{code}
data Vec : ℕ → Set → Set where
  []   :                Vec    zero    a
  _∷_  : a → Vec n a →  Vec (  suc n)  a
\end{code}
(I enjoy writing Agda types these days because I no longer have to quantify over each and every variable, such as |a|~and~|n| in the type of cons --- Agda can do that for me if I give suitable declarations.)
The constructors used in a list of type |Vec n a| are completely determined by the length index~|n|.
The data type definition could even be understood as if it were performing pattern matching on the index: if the index is |zero|, then the list has to be nil; otherwise the index is a |suc|, and the list has to start with a cons.
(About a decade ago a gang of people~\citep{Chapman-levitation, Ko-pcOrn, Dagand-functional-ornaments} did develop theories for defining data types by pattern matching on indices in this way.)

In the same vein, I write down a shape-indexed version of Richard's \lstinline{B}~data type~(\cref{sec:binomial}):
%\Jeremy{For consistency here, we should talk earlier about ``level $k$'' rather than ``level $n$''}
\begin{code}
data B : ℕ → ℕ → Set → Set where
  tipZ  :   a                → B n           zero    a
  tipS  :   a                → B (suc  k) (  suc k)  a
  bin   :   B n (suc  k)  a
        →'  B n       k   a  → B (suc  n) (  suc k)  a
\end{code}
The size of a tree of type |B n k a| with $k \le n$ is precisely the binomial coefficient~|CHOOSE n k|. Naturally, there are no inhabitants when $k > n$.
Like |Vec|, the indices $n, k$ determine the constructors.
If |k|~is |zero|, then the tree is a |tipZ| with one element (|CHOOSE n 0 =' 1|).
Otherwise, if |n|~is |suc k|, then the tree is a |tipS| also with one element (|CHOOSE sk sk =' 1|).
Otherwise the tree is a |bin|, and the sizes |CHOOSE n sk| and |CHOOSE n k| of the two subtrees add up to the expected size |CHOOSE sn sk| of the whole tree.
The trees are now truly \emph{binomial} rather than just binary, formalising Richard's hint about sizes.
I'll write |B(C n k)| for |B n k|, by analogy with |CHOOSE n k|.

And now I can give a more precise type to \lstinline{cd}~(\cref{sec:functions}):
\begin{code}
cd : (SUPPRESSED(1 ≤ k)) → (SUPPRESSED(k < n)) → B(C n k) a → B(C n sk) (Vec (1 + k) a)
\end{code}
It takes as input the data for level~$k$ out of $n$~levels in the sublist lattice~(\cref{fig:sublists-lattice}), with $1 \le k < n$; these are the results for each of the |CHOOSE n k| $k$-sublists of the original $n$-list.
And it returns as output the components for level~|1 + k|; there are |CHOOSE n (sk)| of these, each a |(1 + k)|-list to be fed into \lstinline{g}.
%The input data can conveniently be stored in a tree indexed by $n,k$, and the output indexed by $n,1+k$.

I continue to transcribe the definition of \lstinline{cd} interactively in Agda.
\begin{code}
cd : (SUPPRESSED(1 ≤ k)) → (SUPPRESSED(k < n)) → B(C n k) a → B(C n sk) (Vec (1 + k) a)
cd (bin       (tipS y)        (tipZ z)   ) = tipS  (y ∷ z ∷ [])
cd (bin       (tipS y)   u @  (bin _ _)  ) = tipS  (y ∷ unTipB (cd u))
cd (bin  t @  (bin _ _)       (tipZ z)   ) = bin   (cd t) (mapB (_∷ (z ∷ [])) t)
cd (bin  t @  (bin _ _)  u @  (bin _ _)  ) = bin   (cd t) (zipBWith _∷_ t (cd u))
\end{code}

In the first |bin (tipS y) (tipZ z)| case, Agda conveniently figures out for me whether a \lstinline{Tip} in the pattern should be a |tipS| or |tipZ|.
I expect Agda to fill in the right constructor for the goal type |B(C 2 2) (Vec 2 a)| too, but Agda complains that it cannot decide between |tipS| and |bin|.
Indeed, |B(C 2 2) (Vec 2 a)| matches the result type of both |tipS| and |bin|.
But |bin| is actually impossible because its left subtree would have type |B(C sk ssk) a|, which can be proved to be uninhabited.
So the indices of~|B| still determine the constructor, though not as directly as in the case of |Vec|.

I go through the cases |bin (tipS y) u| and |bin t (tipZ z)| without difficulties, after supplying the definitions of |unTipB  : B(C n n) a → a| and |mapB : (a → b) → B(C n k) a → B(C n k) b|.
In the final |bin t u| case, the result should be a |bin|, and the left subtree |cd t| is accepted by Agda.
Slightly anxiously, I start constructing the right subtree.
Agda tells me that |t : B(C sn ssk) a| and |u : B(C sn sk) a|.
When I ask what type |cd u| has, Agda responds with |B(C sn ssk) (Vec (2 + k) a)|.
That's the same shape as~|t|, so |t|~and |cd u| can be safely zipped together using a shape-preserving |zipBWith : (a → b → c) → B(C n k) a → B(C n k) b → B(C n k) c|.

I've gone through the whole definition!
So, as I guessed, the binomial shape constraint holds throughout |cd|.
What's nice is that I didn't need to do much.
The type checker took care of most of the proof, using the indices to keep track of the tree shapes throughout the transcription.

I've still got a bit of extra proof burden about the two (greyed out) `side conditions' |1 ≤ k| and |k < n|.
Whenever I called |cd|, I checked these conditions mentally and then temporarily ignored them.
(I~wrote `|cd u|' as if |cd| were a function with only one explicit argument.)
Everything related to these conditions was also ignored, including cases that can be proved to be impossible.
Agda ensures that I don't forget about all the ignored stuff in the final code though.

\subsection{Properties in Types}

So much for the shape.
But how do I know that the contents are correct~--- that \lstinline{cd} is correctly rearranging the values?
%\Jeremy{I don't really understand the TODO: ``What to say? Need a spec: the equational one using \lstinline{choose} (marking the element positions with sublists and specifying where the elements should go); but requires a lot of proving''. Update 20240124: A lot of equational reasoning. Do we mention Shin's paper? Josh: This has to be in the Afterword.}

Most likely, the key is parametricity.
The input to \lstinline{cd} is a tree of values associated with $k$-sublists (for some $1 \le k < n$), and these values are rearranged in relation to |(1 + k)|-sublists.
Since \lstinline{cd} is parametric in the type of these values, I can just take |k|-sublists themselves and specify how \lstinline{cd} should rearrange them, and then \lstinline{cd} will have to do the same rearrangement for any type of values.

Formally, the first thing to do is define `|k|-sublists' for arbitrary~|k|.
In Haskell, I suppose Richard might have defined the choice of \lstinline{k}~elements from a list (implicitly of length~\lstinline{n}):
%\Jeremy{shouldn't all occurrences of \lstinline{k+1} be \lstinline{1+k}? Update 20240124: it's complicated. Haskell has \lstinline{n+k} patterns; but Agda used to require \lstinline{1+n}.
%Josh: Coincidentally, using a snoc pattern is more consistent with k+1.}
\begin{lstlisting}
choose :: Int -> L a -> B (L a)
choose    0  _                      =  Tip []
choose (k+1) xs || length xs == k+1  =  Tip xs
choose (k+1) (xs ++ [x])            =  Bin (choose (k+1) xs)
                                           (mapB (++[x]) (choose k xs))
\end{lstlisting}
The pattern-matching structure of \lstinline{choose} is the same as how |B(C n k)| analyses its indices~(\cref{sec:shape}), except that here I need to deal with a list \lstinline{xs} rather than just its length.
The function formalises the pattern I saw in Richard's trees~(\cref{sec:binomial}).
It also generalises Richard's \lstinline{dc} that computes the immediate sublists~(\cref{sec:algorithms}):\csp\lstinline{dc xs}\csp can be redefined as\csp\lstinline{flatten (choose (length xs - 1) xs)}, where
\begin{lstlisting}
flatten :: B a -> L a
flatten (Tip x)   = [x]
flatten (Bin t u) = flatten t ++ flatten u
\end{lstlisting}
Then Richard could have specified \lstinline{cd} by
\begin{equation}
\text{\lstinline{cd (choose k xs)}} \equals \text{\lstinline{mapB (flatten . choose k) (choose (k+1) xs)}}
\tag{$\ast$}
\label{eq:cd-spec}
\end{equation}
Informally: given all the \lstinline{k}-sublists of an \lstinline{n}-list \lstinline{xs}, \lstinline{cd} should rearrange and duplicate them into the appropriate positions for the \lstinline{(k+1)}-sublists, where in the position for a particular \lstinline{(k+1)}-sublist, the result should be the list of all its immediate sublists as computed by \lstinline{flatten . choose k}.

I could finish what Richard could've done in his paper by deriving the definition of \lstinline{cd} from the specification~\cref{eq:cd-spec}.
Maybe I could switch to |B(C n k)| throughout to make the shapes clear.
But there's going to be a large amount of tedious equational reasoning\ldots
I'm not thrilled by the prospect.

\pause

\Josh{No indentation after a pause?}
My editor is still running Agda and showing the shape-indexed version of |cd|, with |B(C n k)| in its type~(\cref{sec:shape}).
The whole point of programming with \emph{inductive families}~\citep{Dybjer-inductive-families} such as |B(C n k)| is to `say more and prove less': encode more properties in the indices, so that those properties are automatically taken care of as programs construct and deconstruct indexed data, requiring fewer manual proofs.
%\Jeremy{Well: the same proofs, but relegating them to the typechecker.}
Instead of just the shapes, maybe it's possible to extend |B(C n k)| and encode the \emph{entire} specification~\cref{eq:cd-spec} of \lstinline{cd} in its type?

What the specification~\cref{eq:cd-spec} says is basically that \lstinline{cd} should transform a tree produced by \lstinline{choose} into another one also produced by \lstinline{choose} and then processed using a \lstinline{mapB}.
I suppose I could force a tree to be the result of \lstinline{mapB h (choose k xs)} for some~\lstinline{h} (which is the common form of the input and output trees of \lstinline{cd}) by adding \lstinline{h} and \lstinline{xs} as indices to |B(C n k)|:
\begin{code}
  data B' : (n k : ℕ) (b : Set) → (Vec k a → b) → Vec n a → Set where
    tipZ  :   (y : b) (e : y ≡ h []  )             → B' n           zero    b h xs
    tipS  :   (y : b) (e : y ≡ h xs  )             → B' (suc  k) (  suc k)  b h xs
    bin   :   B' n (suc  k)  b    h            xs
          →'  B' n       k   b (  h ∘ (x ∷_))  xs  → B' (suc  n) (  suc k)  b h (x ∷ xs)
\end{code}
It's a rather complex extension to |B(C n k)|, but I think I'll be fine if I stick to the same programming methodology: perform `pattern matching' on the indices, and specify what should be in the tree in each case.
In the first case, \lstinline{choose} returns~\lstinline{Tip []}, so the tree should be a |tipZ|, and its element~|y| should be accompanied by a proof~|e| that |y|~equals |h []|, so that |tipZ y e| `is' \lstinline{mapB h (Tip [])}.
The second case is similar.
In the third case, the first thing I do is switch from Richard's snoc pattern \lstinline{xs ++ [x]} to a cons index |x ∷ xs| --- this just `reverses' the list and shouldn't break anything, as long as the snoc in \lstinline{mapB (++[x])} is also switched to a cons consistently.
The first inductive call of \lstinline{choose} easily translates into the type of the left subtree.
The right subtree should be the result of \lstinline{map h (map (x:) (choose k xs))}.
Luckily, the two maps can be fused into a single \lstinline{map (h . (x:))}.
So the type of the second subtree uses the index |h ∘ (x ∷_)| instead of~|h|.

I wasn't fully aware of how complex |B'|~is until I wrote it down.
Even though I sort of derived the data type from a specification and know it should work, I still feel an urge to see with my own eyes that the data type does work as intended.
So I write a tree with `holes' (missing parts of a program) at the element positions, and let Agda tell me what types the holes should have:
\begin{code}
testB' : {b : Set} {h : Vec 2 Char → b} → (B'_ 4 2) b h "abcd"
testB' = bin  (bin  (tipS  (GOAL(b)(G0)) (GOAL(?0 ≡ h "cd")(G1)))
                    (bin  (tipS  (GOAL(b)(G2))  (GOAL(?2 ≡ h "bd")(G3))  )
                          (tipZ  (GOAL(b)(G4))  (GOAL(?4 ≡ h "bc")(G5))  )))
              (bin  (bin  (tipS  (GOAL(b)(G6))  (GOAL(?6 ≡ h "ad")(G7))  )
                          (tipZ  (GOAL(b)(G8))  (GOAL(?8 ≡ h "ac")(G9))  ))
                    (tipZ  (GOAL(b)(G10)) (GOAL(?10 ≡ h "ab")(G11))))
\end{code}
The goal types of the even-numbered holes are all~|b|, and the odd-numbered holes require proofs that the even-numbered holes are equal to |h zs| for all the |2|-sublists |zs| of |"abcd"|.
It works!

\pause

|B'|~doesn't look bad, but I can't help raising an eyebrow.
With yet more effort, I suppose I could refine the type of |cd| to use~|B'| and encode the full specification~\cref{eq:cd-spec}.
But the refined |cd| would need to manipulate the equality proofs in those trees, and maybe eventually I'd still be doing essentially the same tedious equational reasoning that I wanted to avoid.

Another problem is that the upgraded |cd| would only work on trees of sublists, whereas the original \lstinline{cd} in Haskell works on trees of \emph{any} type of values.
Indeed, the specification~\cref{eq:cd-spec} talks about the behaviour of \lstinline{cd} on trees of sublists only.
By encoding the specification in the type, I'd actually restrict |cd| to trees of sublists.
That doesn't sound too useful.

Still, I can't take my eyes off the definition of~|B'|.
The way it absorbs the definition of \lstinline{choose} looks right.
If only the elements aren't restricted to pairs of the form |y : b| and |e : y ≡ h zs|\ldots

A lightbulb lights up above my head.
\begin{code}
data BT : (n k : ℕ) → (Vec k a → Set) → Vec n a → Set where
  tipZ  :   p []                             → BT n           zero    p xs
  tipS  :   p xs                             → BT (suc  k) (  suc k)  p xs
  bin   :   BT n (suc  k)   p            xs
        →'  BT n       k (  p ∘ (x ∷_))  xs  → BT (suc  n) (  suc k)  p (x ∷ xs)
\end{code}
Just generalise the element type!
More specifically, generalise that to a \emph{type family} |p : Vec k a → Set| indexed by |k|-sublists.
Then both |B(C n k) a| and |B'_ n k b h xs| become special cases by specialising~|p| to |const a| (and supplying any |n|-list as the last index) and to |λ zs → Σ[ y ∈ b ] y ≡ h zs| respectively!

I wasn't expecting this generalisation.
After taking a moment to calm down, I look more closely at this new, unifying data type.
The index~|p| in |BT| replaces~|h| in~|B'|, and is similarly applied to all the sublists of a particular length.
What's different is that |p|~is applied to a sublist to get the whole element type in a tip.
So, in general, all the elements in a tree of type |BT_ n k p xs| have \emph{distinct} types, which are |p ys| for all the |k|-sublists |ys| of the |n|-list |xs|.
To see an example:
\begin{code}
testBT : {p : Vec 2 Char → Set} → (BT_ 4 2) p "abcd"
testBT = bin  (bin  (tipS  (GOAL(p "cd")(G0))  )
                    (bin  (tipS  (GOAL(p "bd")(G1))  )
                          (tipZ  (GOAL(p "bc")(G2))  )))
              (bin  (bin  (tipS  (GOAL(p "ad")(G3))  )
                          (tipZ  (GOAL(p "ac")(G4))  ))
                    (tipZ  (GOAL(p "ab")(G5))  ))
\end{code}
It's simpler to think of a tree of type |BT_ n k p xs| as a table with all the |k|-sublists of~|xs| as the keys. For each key~|ys|, there's an entry of type |p ys|.
(So the `T' in |BT| stands for both `tree' and `table'.)
%\Josh{We could explain in more detail how to find a key in a tree, but that doesn't seem too important because we don't work with individual entries but all the entries about all the sublists of a particular length at once, and the position of each entry in the tree is not important.}

This |BT| definition is really intriguing\ldots
My mind starts to wander.
The ad hoc feeling I had with~|B'| is completely gone.
This is probably because there's no arbitrary information in |BT| with respect to \lstinline{choose}.
\Shin{Does it mean there is no unnecessary information apart from those relevant to \lstinline{choose}, or there is no information about \lstinline{choose}?}
Most likely, there is a way to derive |BT| from \lstinline{choose}, and that'll work for a whole class of functions.
I mean, the type of |BT_ n k : (p : Vec k a → Set) → Vec n a → Set| is a continuation-passing version of some |Vec n a ↝ Vec k a|, which would be the (shape-indexed) type of a version of \lstinline{choose} that non-deterministically returns a sublist.
And the index~|p| works like a continuation too.
Take the (expanded) type of |bin| for example:
\begin{code}
bin  :   BT n (suc  k)  (λ ys  → p ys)        xs
     →'  BT n       k   (λ zs  → p (x ∷ zs))  xs  → BT (suc n) (suc k) p (x ∷ xs)
\end{code}
I can read it as `to compute a |(1 + k)|-sublist of |x ∷ xs| and pass it to continuation~|p|, either compute a |(1 + k)|-sublist |ys| of |xs| and pass |ys| to |p| directly, or compute a |k|-sublist |zs| of |xs| and pass |x ∷ zs| to~|p|'.
All the results from |p| are then collected in a tree as the indices of the element types.
%\Shin{Changed some ``return'' to ``pass'' and added ``to |p|'', ``from |p|'' etc., to make it clearer --- if my understanding is correct.}
Another similar and familiar example is
\begin{code}
data All : (a → Set) → Vec n a → Set where
  []   :                   All p []
  _∷_  : p x → All p xs →  All p (x ∷ xs)
\end{code}
which should be derivable from the function that non-deterministically returns an element of a list.
I'm onto something general --- maybe it's interesting enough for an ICFP paper!
%\Josh{A paragraph about generality --- worth saying? Make it clear that the paragraph is about future work.}

\subsection{Specifications as Types}
\label{sec:spec}

That paper will have to wait though.
I've still got a problem to solve: how do I use |BT| to specify \lstinline{cd}?

What's special about |BT| is that the element types are indexed by sublists, so I know from the type of an element with which sublist it is associated.
\Shin{"I know from the type of an element which sublist it is associated."? Should there be a "with"?}
That is, I can now directly say `values associated with sublists' and how they should be rearranged, rather than indirectly specify the rearrangement in terms of sublists and then extend to other types of values through parametricity.
|BT_ n k p xs| is the type of a tree of |p|-typed values associated with the |k|-sublists of |xs|, and that's precisely the intended meaning of \lstinline{cd}'s input.
What about the output?
It should tabulate the |(1 + k)|-sublists of |xs|, so the type should be |BT_ n sk q xs| for some |q : Vec (1 + k) a → Set|.
For each sublist |ys : Vec (1 + k) a|, I~want a list of |p|-typed values associated with the immediate sublists of |ys|, which are |k|-sublists.
Or, instead of a list, I can just use a tree of type |BT_ sk k p ys|.
Therefore the whole type is
\begin{code}
retabulate : (SUPPRESSED(k < n)) → (BT_ n k) p xs → (BT_ n sk) ((BT_ sk k) p) xs
\end{code}
which is parametric in~|p| (so, like the Haskell version of \lstinline{cd}, the elements can have any types).
I think it's time to rename \lstinline{cd} to something more meaningful, and decide to use `|retabulate|' because I'm moving values in a table into appropriate positions in a new (nested) table with a new tabulation scheme.
% \Jeremy{I'd like to think of a better name. } % Happy now!
And a side condition |k < n| is needed to guarantee that the output shape |BT_ n sk| is valid.
%\Shin{In the following paragraphs I try to describe how |retabulate| can be constructed from its type. Some changes were made: 1. |_∷ᴮᵀ_| is introduced earlier and slightly more detailed because I will use it later. 2. definition of |mapBT| is omitted because I think it is probably not needed and now we might be running out of space. BTW, I don't know how to say ``everything related to |k < n| is omitted'' in an early stage, therefore all my calls to |retabulate| still have the |k < n| argument in underline. It is preferable to find a reason to omit it. Josh: I think it's fine to assume that they're only managed mentally (and not formally in Agda) in the `first pass' presented in the paper, like what we did when transcribing \lstinline{cd}.}

The type of |retabulate| looks like a sensible refinement of the type of \lstinline{cd}, except that I'm letting |retabulate| return a tree of trees, rather than a tree of lists.
Could that change be too drastic?
Hm\ldots actually, no --- the shape of |BT_ sk k| is always a (non-empty) list!
If |k|~is |zero|, a |BT_ 1 0|-tree has to be a |tipZ|.
Otherwise, a |BT_ ssk sk|-tree has to take the form |bin (tipS y) t|.
This expression is in fact a cons-like operation:
\begin{code}
_∷ᴮᵀ_ : p xs → BT(C sk k) (p ∘ (x ∷_)) xs → BT(C ssk sk) p (x ∷ xs)
y ∷ᴮᵀ t = bin (tipS y) t
\end{code}
To construct a table indexed by all the immediate sublists of |x ∷ xs|, I need an entry for |xs|, the immediate sublist without~|x|, and a table of entries for all the other immediate sublists, which are |x ∷ ws| for all the immediate sublists |ws| of |xs|.

I go on to define |retabulate|.
Its type is much more informative than that of \lstinline{cd}.
Rather than transcribing \lstinline{cd}, can its type guide me through the implementation?
I type the left-hand side of |retabulate| into the editor, leave the right-hand side as a hole, and perform some case splitting on the input tree:
\begin{spec}
retabulate (tipZ _)                                  = (GOAL(BLANK)(G0))
retabulate (tipS _)                                  = (GOAL(BLANK)(G1))
retabulate (bin      (tipS _)     _               )  = (GOAL(BLANK)(G2))
retabulate (bin      (bin _ _  )       (tipZ _)   )  = (GOAL(BLANK)(G3))
retabulate (bin      (bin _ _  )       (tipS _)   )  = (GOAL(BLANK)(G4))
retabulate (bin t @  (bin _ _  )  u @  (bin _ _)  )  = (GOAL(BT_ ssn sssk ((BT_ sssk ssk p) (x ∷ x₁ ∷ xs)))(G5))
\end{spec}
The cases for |tipS _| and |bin _ (tipS _)| can be eliminated immediately since the side condition |k < n| is violated.
I go straight to the last and the most difficult case, |bin t u|, where |t|~and~|u| are both constructed by |bin|.
Their types are
\begin{spec}
t  : BT(C sn ssk) p (x₁ ∷ xs)
u  : BT(C sn sk) (p ∘ (x ∷_)) (x₁ ∷ xs)
\end{spec}
Neither of them have the right shape to be used immediately, so in |(GOAL(BLANK)(G5))| I try starting with a |bin|:
\begin{spec}
retabulate (bin t @ (bin _ _) u @ (bin _ _)) = bin  (GOAL(BT(C sn sssk) (BT(C sssk ssk) p) (x₁ ∷ xs))(G6))
                                                    (GOAL(BT(C sn ssk) (BT(C sssk ssk) p ∘ (x ∷_)) (x₁ ∷ xs))(G7))
\end{spec}
|(GOAL(BLANK)(G6))| is directly fulfilled by the induction hypothesis |retabulate t|!
That's a good sign.

What can I put in |(GOAL(BLANK)(G7))|?
Prompted by the success with |(GOAL(BLANK)(G6))|, I try the induction hypothesis for~|u|:
\begin{spec}
retabulate u : BT(C sn ssk) (BT (C ssk sk) (p ∘ (x ∷_))) (x₁ ∷ xs)
\end{spec}
Hm.
Its type has the same outer shape |BT(C sn ssk) _ (x₁ ∷ xs)| that I want in the goal type, but the element types don't match\ldots

To fill out |(GOAL(BLANK)(G7))| I really have to pay more attention to what the types say.
I stare at the types, and, slowly, they start to make sense.
\begin{itemize}[leftmargin=*]
\item The outer shape |BT(C sn ssk) _ (x₁ ∷ xs)| tells me that I'm dealing with tables indexed by the |(2 + k)|-sublists |zs| of |x₁ ∷ xs|.
\item For each |zs|, I need to construct a table of |p|-typed entries indexed by all the immediate sublists of |x ∷ zs|, because that's what the element types |BT(C sssk ssk) p ∘ (x ∷_)| in the goal type mean.
\item What do I have in |retabulate u|?
I have a table of entries indexed by |x ∷ ws| for all the immediate sublists |ws| of |zs| in |retabulate u| --- that's what the element types |BT (C ssk sk) (p ∘ (x ∷_))| mean.
\item What's the relationship between these sublists |x ∷ ws| and the table I need to construct, which is indexed by the immediate sublists of |x ∷ zs|?
Oh right, the sublists |x ∷ ws| are all the immediate sublists of |x ∷ zs| with the first element~|x|!
So I've already got most of the entries I need.
\item I'm still missing an entry for the immediate sublist of |x ∷ zs| without~|x|, which is |zs|.
Do I have that?
I search through the context.
The type of~|t| catches my attention: it has the familiar outer shape |BT(C sn ssk) _ (x₁ ∷ xs)|.
What entries are in~|t|?
Its type tells me that there's an entry for each |(2 + k)|-sublist |zs| of |x₁ ∷ xs|.
That's precisely what I'm missing!
\end{itemize}
So, for each |zs|, I can construct a table indexed by the immediate sublists of |x ∷ zs| by combining an entry for |zs| (the immediate sublist without~|x|) from~|t| with a table of entries for all the other immediate sublists (with~|x|) from |retabulate u|.
An entry and a table of entries --- aren't they exactly the arguments of |_∷ᴮᵀ_|\,?
Indeed, I can fulfil |(GOAL(BLANK)(G7))| by combining all the corresponding entries in~|t| and |retabulate u| (that share the same index |zs|) using |_∷ᴮᵀ_|\,, that is, |zipBTWith _∷ᴮᵀ_ t (retabulate u)|!

The rest of the cases are much easier, and I come up with a definition of |retabulate|,
\begin{code}
retabulate : (SUPPRESSED(k < n)) → BT(C n k) p xs → BT(C n sk) (BT(C sk k) p) xs
retabulate {xs =' _ ∷ []     } (tipZ y) = tipS  (tipZ y)
retabulate {xs =' _ ∷ _ ∷ _  } (tipZ y) = bin   (retabulate (tipZ y)) (tipZ (tipZ y))
retabulate (bin       (tipS y)   u               ) = tipS  (y ∷ᴮᵀ u)
retabulate (bin  t @  (bin _ _)       (tipZ z)   ) = bin   (retabulate t) (mapBT (_∷ᴮᵀ (tipZ z)) t)
retabulate (bin  t @  (bin _ _)  u @  (bin _ _)  ) = bin   (retabulate t)
                                                           (zipBTWith _∷ᴮᵀ_ t (retabulate u))
\end{code}
where the map and zip functions are the expected ones:
\begin{spec}
mapBT      : (  ∀ {ys} → p ys → q ys) → ∀ {xs} → (BT_ n k) p xs → (BT_ n k) q xs
zipBTWith  : (  ∀ {ys} → p ys → q ys → r ys)
           →'   ∀ {xs} → (BT_ n k) p xs → (BT_ n k) q xs → (BT_ n k) r xs
\end{spec}
%The impossible cases are omitted, so is everything related to the side condition |k < n|, to make it easier to compare with \lstinline{cd}.

%I go on and transcribe \lstinline{cd} into |retabulate|,
%\begin{code}
%retabulate : (SUPPRESSED(k < n)) → BT(C n k) p xs → BT(C n sk) (BT(C sk k) p) xs
%retabulate {xs =' _ ∷ []     } (tipZ y) = tipS  (tipZ y)
%retabulate {xs =' _ ∷ _ ∷ _  } (tipZ y) = bin   (retabulate (tipZ y)) (tipZ (tipZ y))
%retabulate (bin       (tipS y)   u               ) = tipS  (y ∷ᴮᵀ u)
%retabulate (bin  t @  (bin _ _)       (tipZ z)   ) = bin   (retabulate t) (mapBT (_∷ᴮᵀ (tipZ z)) t)
%retabulate (bin  t @  (bin _ _)  u @  (bin _ _)  ) = bin   (retabulate t)
%                                                           (zipBTWith _∷ᴮᵀ_ t (retabulate u))
%\end{code}
%where the map function is the expected one,
%\begin{code}
%mapBT : (∀ {ys} → p ys → q ys) → ∀ {xs} → (BT_ n k) p xs → (BT_ n k) q xs
%mapBT f (tipZ  p)  = tipZ  (f p)
%mapBT f (tipS  p)  = tipS  (f p)
%mapBT f (bin t u)  = bin   (mapBT f t) (mapBT f u)
%\end{code}
%and a cons function can be introduced for |BT_ sk k|-trees/lists:
%\begin{code}
%_∷ᴮᵀ_ : p xs → BT(C sk k) (p ∘ (x ∷_)) xs → BT(C ssk sk) p (x ∷ xs)
%y ∷ᴮᵀ t = bin (tipS y) t
%\end{code}
%(The type of |_∷ᴮᵀ_| is slightly complex, but Agda pretty much infers it for me.)
%Everything related to the side condition |k < n| is omitted to make it easier to compare |retabulate| with \lstinline{cd}; also omitted are the two cases |tipS _| and |bin _ (tipS _)|, whose shapes are proved to be impossible.
%I forgot about another side condition |1 ≤ k|, but that leads to two additional |tipZ| cases (which are fairly easy to figure out from the type information) instead of preventing me from completing the definition.

Amazingly, the more informative type of |retabulate| did help me to develop its definition.
As I filled in the holes, I didn't feel I had much of a choice --- in a good way, because that reflected the precision of the type.
Furthermore, I discovered a new algorithm that varies slightly from Richard's \lstinline{cd}!
The first two cases of \lstinline{cd} are subsumed by the third case, |bin (tipS y) u|, of |retabulate|.
The second case of \lstinline{cd} recursively traverses the given tree to convert it to a list, which is not needed in |retabulate|, because it yields a tree of trees.
Therefore the first two cases of \lstinline{cd} can be unified into one.
Meanwhile, the first two cases of |retabulate| concerning |tipZ| are new.
Whereas \lstinline{cd} has to start from level~$1$ of the sublist lattice~(\cref{fig:sublists-lattice}), this pair of cases of |retabulate| is capable of producing a level-$1$ table (with as many elements as |xs|) from a level-$0$ table, which is a |tipZ|.
This is due to |xs| now being available as an index, providing the missing context for |retabulate|.
%The definition has been verified simply by finding a right type for it!
%There's actually no need to understand the definition of \lstinline{cd}/|retabulate| now, but I can still go through a case or two to see how well type-directed programming works.

%\todo[inline]{Compare \lstinline{cd} and |retabulate|.
%(In particular, the additional |tipZ| cases of |retabulate| are responsible for producing a level-1 table (with as many elements as |xs|) from a level-0 table, which is a |tipZ|.
%Since |xs|~is available as an index, there's now enough information for going from level~0 to level~1 (on the sublist lattice).)
%The definition has been verified simply by finding the (or rather, a) right type for it!
%There's actually no need to understand the definition of \lstinline{cd}/|retabulate| now, but I can still go through a case or two to see how well type-directed programming works.}

In fact, looking at the type more closely, I suspect that the extensional behaviour of |retabulate| is completely determined by the type (so the type works as a nice and tight specification): the shape of the output table is completely determined by the indices; moreover, all the input elements have distinct types in general, so each element in the output table has to be the only input element with the required type --- there is no choice to make.
Formally, the proof will most likely be based on parametricity (and might be similar to \varcitet{Voigtlander-BX-for-free}{'s}).
That'll probably be a fun exercise\ldots but I'll leave that for another day.

\subsection{Equality from Types}
\label{sec:equality-from-types}

Right now I'm more eager to find out why the bottom-up algorithm \lstinline{bu} equals the top-down \lstinline{td}~(\cref{sec:algorithms,sec:bu}).
Will dependent types continue to be helpful?
I should try and find out by transcribing the two algorithms into Agda too.

I go back to the type of the combining function~\lstinline{g}.
This type \lstinline{L s -> s}
has been making me shudder involuntarily whenever I see it: it says so little that \lstinline{g}~could have arbitrarily wild behaviour. That's rather unsettling.
The intention ---~that \lstinline{g}~should compute the solution for a list from those of its immediate sublists~--- is nowhere to be seen.
%\Josh{The type of~\lstinline{g} is actually not parametric in~\lstinline{b}, but \lstinline{b}~is parametrically quantified in a bigger context; worth clarifying (throughout the paper, and for Agda code too)?}

But now I have the right vocabulary to state the intention precisely in Agda.
I can use |BT| to say things about all sublists of a particular length.
And to say `a solution for a list' (instead of just `a solution') I should switch from a type to a type family
\begin{code}
s : ∀ {k} → Vec k a → Set
\end{code}
such that |s ys| is the type of solutions for |ys|.
So
\begin{temp}
\begin{code}
g : ∀ {k} → {ys : Vec (2 + k) a} → BT(C ssk sk) s ys → s ys
\end{code}
\end{temp}
I look at this with a satisfied smile --- now that's what I call
%\Jeremy{British pop-cultural reference}
a nice and informative type!
It says concisely and precisely what |g|~does: compute a solution for any |ys : Vec (2 + k) a| from a table of solutions for all the length-|(1 + k)| (that is, immediate) sublists of |ys|.

The smile quickly turns into a frown though.
I still don't feel comfortable with |BT(C ssk sk)|.
The indices are apparently not the most general ones --- why not |BT(C sk k)|?

I delete~(\ding{56}) the type of~|g| and start pondering.
\Jeremy{Saying this here is a bit awkward\ldots Josh: How about this?}
I wrote |BT(C ssk sk)| in that type because that was what Richard wanted to say.
Richard used singleton lists as the base cases instead of the empty list, so \lstinline{g}~was applied to solutions for sublists of length at least~|1|, hence the subscript |1 + k|.
But the most general type
\begin{code}
g : ∀ {k} → {ys : Vec (1 + k) a} → BT(C sk k) s ys → s ys
\end{code}
looks just fine.
In particular, when |k|~is~|0|, the type says that |g|~should compute a solution for a singleton list from a solution for the empty list (the only immediate sublist of a singleton list), which seems reasonable\ldots

\begin{aha}
\ldots And indeed it is reasonable!
\end{aha}

When I discovered the extra |tipZ| cases of |retabulate|~(\cref{sec:spec}), I saw that it may be possible to start from level~0 of the sublist lattice~(\cref{fig:sublists-lattice}) after all.
Now it's confirmed.
Instead of starting with solutions for singleton lists, I can start with a given solution for the empty list
\begin{temp}
\begin{code}
e : s []
\end{code}
\end{temp}
at level~0, and work upwards using~|g|.
There's no problem going from level~0 to level~1, because there's now additional context in the indices so that |g|~knows for which singleton list a solution should be computed.
Making types precise has helped me to find a more natural and general form of recursive computation over immediate sublists!

And it's not just any recursive computation --- it's now an alternative \emph{induction principle} for lists!
The base case~|e| is still about the empty list, and the inductive case~|g| assumes that the induction hypothesis holds for all the immediate sublists.
(I~guess I've been instinctively drawn towards induction principles, in common with most dependently typed programmers.)
\begin{temp}
\begin{code}
ImmediateSublistInduction : Set₁
ImmediateSublistInduction =
  {a : Set}  (  s   : ∀ {k} → Vec k a → Set)
             (  e   : s [])
             (  g   : ∀ {k} → {ys : Vec (1 + k) a} → BT(C sk k) s ys → s ys)
  {n : ℕ}    (  xs  : Vec n a) → s xs
\end{code}
\end{temp}

\pause

|ImmediateSublistInduction| looks very nice, but I'm still worried: will it be possible to transcribe \lstinline{td} and \lstinline{bu} for this type nicely, that is, without ugly stuff like type conversions (|subst|, |rewrite|, etc)?

Sadly, there may never be any theory that tells me quickly whether or not a type admits nice programs.
The only way to find out is to try writing some!
I start transcribing \lstinline{td}~(\cref{sec:algorithms}).
The only component for which I still don't have a dependently typed version is \lstinline{dc}, which I've generalised to \lstinline{choose}~(\cref{sec:spec}).
Transcribing \lstinline{choose} is mostly a standard exercise in dependently typed programming:
\begin{code}
choose : (n k : ℕ) → k ≤↑ n → (xs : Vec n a) → BT(C n k) Exactly xs
choose _           zero    _          _         = tipZ  (exactly []  )
choose (suc k)  (  suc k)     zero    xs        = tipS  (exactly xs  )
choose (suc n)  (  suc k)  (  suc d)  (x ∷ xs)  =
  bin (choose n (suc k) d xs) (mapBT (mapExactly (x ∷_)) (choose n k (incr d) xs))
\end{code}
The key ingredient is the |BT(C n k)| in the result type, which tabulates all the |k|-sublists as the indices of the element types.
I just need to plug in this data type
\begin{code}
data Exactly : a → Set where
  exactly : (x : a) → Exactly x
\end{code}
to say that the elements in the resulting table should be exactly the tabulated indices.
Its map function is straightforward:
\begin{code}
mapExactly : (f : a → b) → Exactly x → Exactly (f x)
mapExactly f (exactly x) = exactly (f x)
\end{code}
The definition of |choose| first performs an induction on~|k|, like the Haskell version.
In contrast to Haskell, I need to make the Agda function total by saying explicitly that the length~|n| of the list |xs| is at least~|k|, so that there are enough elements to choose from.
Somewhat notoriously, there are many versions of natural number inequality.
The version needed here is a data type |m ≤↑ n| where |m|~remains fixed throughout the definition and serves as an `origin', and an inhabitant of |m ≤↑ n| is the distance (which is essentially a natural number) that |n|~is away from the origin~|m|:
\begin{code}
data _≤↑_ : ℕ → ℕ → Set where
  zero  :           m ≤↑ m
  suc   : m ≤↑ n →  m ≤↑ suc n
\end{code}
The second and third cases of |choose| are an inner induction on the distance that |n|~is away from |suc k|.
In the second case the distance is |zero|, meaning that |n|~is (at the origin) |suc k|, so |xs| has the right length and can be directly returned.
Otherwise the distance is |suc d| in the third case, where the first inductive call is on~|d|, and the second inductive call is on~|k| while the distance is unchanged, but the type |suc k ≤↑ suc n| needs to be adjusted to |k ≤↑ n| by invoking this |incr| function on~|d|:
\begin{code}
incr : suc m ≤↑ n → m ≤↑ n
incr    zero    = suc zero
incr (  suc d)  = suc (incr d)
\end{code}

\pause

\Josh{Too much space before the pause}
I step back and take another look at |choose|.
One thing starts to bother me: |Exactly x| is a type that has a unique inhabitant, so I could've used the unit type~|⊤| as the element type instead, and I'd still give the same amount of information, which is none!
That doesn't make a lot of sense --- I thought I was computing all the |k|-sublists and returning them in a table, but somehow those sublists didn't really matter, and I could just return a blank table of type |BT(C n k) (const ⊤) xs|\ldots?

\begin{aha}
Hold on, it's actually making sense\ldots
\end{aha}

It's because all the information is already in the table structure of |BT|.
Indeed, I can write
\begin{code}
mapBT (λ { {ys} tt → exactly ys }): BT(C n k) (const ⊤) xs → BT(C n k) Exactly xs
\end{code}
to recover a table of |Exactly|s from just a blank table by replacing every |tt| (the unique inhabitant of~|⊤|) with the index |ys| there.
What |choose| does is not really compute the sublists --- |BT| has already `computed' them.
Instead, |choose| merely affirms that there is a table indexed by all the |k|-sublists of an |n|-list whenever |k ≤↑ n|.
The elements in the table don't matter, and might as well be |tt|.

So, instead of |choose|, I can use
%\Shin{I find |blank| clearer if we include |xs| as an simplcit argument\ldots\ Josh: Added.}
\begin{temp}
\begin{code}
blank : (n k : ℕ) → k ≤↑ n → {xs : Vec n a} → BT(C n k) (const ⊤) xs
blank _          zero    _                  = tipZ tt
blank (suc k) (  suc k)     zero            = tipS tt
blank (suc n) (  suc k)  (  suc d) {_ ∷ _}  = bin (blank n (suc k) d) (blank n k (incr d))
\end{code}
\end{temp}
to construct a blank table indexed by all the immediate sublists in the inductive case of |td|, where I'll then compute and fill in solutions for all the immediate sublists by invoking |td| inductively, and finally invoke~|g| to combine all those solutions.
%(Since |blank| is again related to binomial coefficients, I'm writing |blank(C n k)| for |blank n k|.)
And the base case simply returns~|e|.
\begin{temp}
\begin{code}
td : ImmediateSublistInduction
td s e g {zero   } []  = e
td s e g {suc n  } xs  = g (mapBT (λ { {ys} tt → td s e g {n} ys }) (blank(C sn n) (suc zero)))
\end{code}
\end{temp}

I look aghast at the monster I've created.
Sure, the definition type-checks, but oh my\ldots it's terribly ugly.
The problems are cosmetic though, and should be easy to fix.
\begin{inlineenum}
\item The induction is on~|n|, which shouldn't have been an implicit argument.
\item In the base case, I have to match |xs| with~|[]| to make it type-correct to return~|e|, but that could've been avoided if I set |e : {xs : Vec 0 a} → s xs|.
\item In the inductive case, |xs| doesn't need to be explicit because it's passed around only implicitly in the indices on the right-hand side.
\item I can get rid of the~|λ| around the inductive call to |td| if I make |ys| implicit and add a dummy |⊤|~argument.
\end{inlineenum}
In fact, if I add a dummy |⊤|~argument to |e|~and |blank| as well, I can make the definition point-free like in Richard's paper --- a temptation I cannot resist!
So I revise the induction principle,
\begin{code}
ImmediateSublistInduction : Set₁
ImmediateSublistInduction =
  {a : Set}  (  s  : ∀ {k} → Vec k a → Set)
             (  e  : {ys : Vec 0 a} → ⊤ → s ys)
             (  g  : ∀ {k} → {ys : Vec (1 + k) a} → BT(C sk k) s ys → s ys)
             (  n  : ℕ) {xs : Vec n a} → ⊤ → s xs
\end{code}
add the dummy |⊤|~argument to |blank| (also ignoring the inequality argument from now on),
\begin{code}
blank : (n k : ℕ) → (SUPPRESSED(k ≤↑ n)) → {xs : Vec n a} → ⊤ → BT(C n k) (const ⊤) xs
\end{code}
and get my point-free |td|:
\begin{code}
td : ImmediateSublistInduction
td s e g    zero    = e
td s e g (  suc n)  = g ∘ mapBT (td s e g n) ∘ blank(C sn n)
\end{code}
The revised |ImmediateSublistInduction| may not be too user-friendly, but that can be amended later (when there's actually a user).

\pause

And it'll be wonderful if the revised |ImmediateSublistInduction| works for |bu| too!
I proceed to transcribe \lstinline{bu}~(\cref{sec:bu}):
\begin{code}
bu : ImmediateSublistInduction
bu s e g n = unTip ∘ loop 0 (GOAL(0 ↓≤ n)(G0)) ∘ mapBT e ∘ blank(C n 0)
  where
    loop : (k : ℕ) → k ↓≤ n → BT(C n k) s xs → BT(C n n) s xs
    loop n    zero    = id
    loop k (  suc d)  = loop (1 + k) d ∘ mapBT g ∘ retabulate
\end{code}
I construct the initial table by reusing |blank| to create a blank level-|0| table and using |mapBT e| to fill in the initial solution for the empty list.
Then the |loop| function increases the level to~|n| by repeatedly retabulating a level-|k| table as a level-|(1 + k)| table and filling in solutions for all the length-|(1 + k)| sublists using~|g|.
Finally, a solution for the whole input list is extracted from the level-|n| table using
\begin{code}
unTip : BT(C n n) p xs → p xs
unTip             (tipS  p) = p
unTip {xs =' []}  (tipZ  p) = p
\end{code}
The argument/counter~|k| of |loop| should satisfy the invariant |k ↓≤ n|.
The data type |m ↓≤ n| is another version of natural number inequality, which is dual to |_≤↑_| in the sense that |n|~is fixed throughout the new definition, and |m|~moves away from~|n|:
\begin{code}
data _↓≤_ : ℕ → ℕ → Set where
  zero  :               n  ↓≤' n
  suc   : suc m ↓≤ n →  m  ↓≤' n
\end{code}
The |loop| function performs induction on the distance |k ↓≤ n|; the counter~|k| goes up as the distance decreases in inductive calls, and eventually reaches~|n| when the distance becomes |zero|.
The remaining |(GOAL(0 ↓≤ n)(G0))| is actually non-trivial, but the Agda standard library covers that.

\begin{aha}
Another nice-looking implementation of |ImmediateSublistInduction|!
\end{aha}

\pause

Okay, I've made the type of both |td| and |bu| precise.
How does this help me prove |td| equals |bu|?
The definitions still look rather different except for their type\ldots

\begin{aha}
\ldots And the type is an induction principle.
\end{aha}

\begin{aha}
Is it possible to have extensionally different implementations of an induction principle?
\Josh{Don't know how to fix the spacing between two aha environments\ldots}
\end{aha}

Let me think about the induction principle of natural numbers.
\begin{code}
ℕ-Induction : Set₁
ℕ-Induction =  (p   : ℕ → Set)
               (pz  : p zero)
               (ps  : ∀ {m} → p m → p (suc m))
               (n   : ℕ) → p n

ind : ℕ-Induction
ind p pz ps     zero    = pz
ind p pz ps (   suc n)  = ps (ind p pz ps n)
\end{code}
The motive~|p| is parametrically quantified, so a proof of |p n| has to be |n|~applications of |ps| to |pz|.
There are intensionally different ways to construct that (|ind| versus a tail-recursive implementation, for example), but extensionally they're all the same.

Of course, parametricity is needed to prove that formally.
I look up \varcitet{Bernardy-proofs-for-free}{'s} translation, which gives the following statement (after a bit of simplification):
\begin{code}
ℕ-Induction-unary-parametricity : ℕ-Induction → Set₁
ℕ-Induction-unary-parametricity f =
  {p   : ℕ → Set}                  (q   : ∀ {m} → p m → Set)
  {pz  : p zero}                   (qz  : q pz)
  {ps  : ∀ {m} → p m → p (suc m)}  (qs  : ∀ {m} {x : p m} → q x → q (ps x))
  {n   : ℕ} → q (f p pz ps n)
\end{code}
Unary parametricity can be thought of as adding an invariant~(|q|) to a parametrically quantified type or type family; this invariant is assumed to hold for any first-order input~(|qz|) and be preserved by any higher-order input~(|qs|), and is guaranteed to hold for the output.
Now choose the invariant that any proof of |p m| is equal to the one produced by |ind p pz ps m|, and that's it:
\begin{code}
ℕ-Induction-uniqueness-from-parametricity :
     (f : ℕ-Induction) → ℕ-Induction-unary-parametricity f
  →  (p : ℕ → Set) (pz : p zero) (ps : ∀ {m} → p m → p (suc m)) (n : ℕ)
  →  f p pz ps n ≡ ind p pz ps n
ℕ-Induction-uniqueness-from-parametricity f param p pz ps n =
  param (λ {m} x → x ≡ ind p pz ps m) refl (cong ps)
  -- |cong : (f : a → b) → x ≡ y → f x ≡ f y|
\end{code}
The same argument works for |ImmediateSublistInduction| --- any function of the type satisfying unary parametricity is pointwise equal to |td|.
I finish the Agda proofs for both induction principles in a dreamlike state.

\begin{aha}
Yeah, I have a proof that |td| equals |bu|.\Jeremy{Julie thought these one-line paragraphs look a bit messy. She suggested adding some space above and below. How is this? Josh: I like the spacing locally, but globally it almost look like a displayed equation (or, indeed, a quote), so there's some unintended emphasis, which may be confusing.}
\end{aha}

Well, strictly speaking I don't have one yet.
(Vanilla) Agda doesn't have internal parametricity~\citep{Van-Muylder-internal-parametricity}, so I'd need to prove the parametricity of |bu|, painfully.
But there shouldn't be any surprise.

Somehow I feel empty though.
I was expecting a more traditional proof based on equational reasoning.
This kind of proof may require more work, but allows me to compare what |td| and |bu| do \emph{intensionally}.
That's an aspect overlooked from the parametricity perspective.
Despite having a proof now, I think I'm going to have to delve into the definitions of |td| and |bu| anyway, to get a clearer picture of their relationship.

\section{Diagrams}

%\todo[inline]{Not a category theory tutorial; more like a companion to a tutorial or a textbook, or an invitation to learn categorical tools (as well as dependent types and string diagrams for that matter) by providing intuitions and practical examples from the immediate-sublist computation; mention this meta-level goal in the abstract and the afterword.}

Another hint Richard left was `naturality', a category-theoretic notion which he used a lot in his paper.
In functional programming, naturality usually stems from parametric polymorphism: all parametric functions, such as \lstinline{cd} and \lstinline{unTip}, satisfy naturality.
I've got some parametric functions too, such as |retabulate| and |unTip|.
Their dependent function types with all the indices are more advanced than Richard's types though, and the simply typed form of naturality Richard used no longer makes sense.
But one nice thing about category theory is its adaptability --- all I need to figure out is which category I'm in, and then I'll be able to work out what naturality means for my functions systematically within the world of category theory.

And, if the key is naturality, now I have an additional tool that Richard didn't: string diagrams.
I've seen how dramatically string diagrams simplify proofs using naturality (and also various other kinds of proof, for which the simplification can be even more dramatic), so it's probably worthwhile to take a look at the two algorithms from a string-diagrammatic perspective.

But before I get to string diagrams, I need to work through some basic category theory\ldots

\subsection{From Categories to String Diagrams}

Functional programmers are familiar with types and functions, and know when functions can be composed sequentially --- when adjacent functions meet at the same type.
And it's possible to compose an empty sequence of functions, in which case the result is an identify function.
\emph{Categories} are settings in which the same intuition about sequential composition works.
Instead of types and functions, the categorical programmer can switch to work with some \emph{objects} and \emph{morphisms} specified by a category, where each morphism is labelled with a source object and a target object (like the source and target types of a function), and morphisms can be composed sequentially when adjacent morphisms meet at the same object.
And, like identity functions, there are identity morphisms too.
Working in a new setting that's identified as a category
%(or some crazier variant that supports more operations in addition to sequential composition)
is a blessing for the functional programmer: it means that the programmer can still rely on some of their intuitions about types and functions to navigate in the new setting.
%(And the formal definitions of various kinds of category make precise which intuitions remain reliable.)
More importantly, some notions that prove to be useful in functional programming (such as naturality) can be defined generically on categories and systematically transported to other settings.

A clue about the kind of category I'm in is that I'm tempted to say `|retabulate| transforms a tree of |p|'s to a tree of trees of |p|'s'.
When a simply typed functional programmer says `a tree of something', that `something' is a type, that is, an object in the category |Fun| of types and functions.
But here |p|~is not a type.
It's a type family.
So I've left |Fun| and landed in a kind of category where the objects are type families.

There are quite a few versions of `categories of families'.
I go through the types of the components used in the algorithms~(\cref{sec:equality-from-types}) to find a common form, and it seems that the simplest version suffices: given an index type |a : Set|, a category of families |Fam' a| has objects of type
\begin{code}
Fam : Set → Set₁
Fam a = a → Set
\end{code}
and morphisms of type
\begin{code}
_⇉_ : Fam a → Fam a → Set
p ⇉ q = ∀ {x} → p x → q x
\end{code}
That is, a morphism from~|p| to~|q| is a family of functions between corresponding types (with the same index) in |p|~and~|q|.
Everything in the definition is parametrised by~|a|, so actually I'm working in not just one but many related categories of families, with different index types.
These categories are still inherently types and functions, so it's no surprise that their sequential composition works in the way familiar to the functional programmer.

With the definition of |Fam'|, now I can rewrite the parametric function types of |retabulate| and |unTip| to look more like the ones in Haskell:
\begin{code}
retabulate  :  BT(C n k) p   ⇉' BT(C n sk) (BT(C sk k) p)
unTip       :  BT(C n n) p   ⇉' p
\end{code}
I can fit |blank(C n k)| into |Fam' (Vec n a)| by lifting its |⊤|~argument to a type family |const ⊤| (that is, an object of the category):
\begin{code}
blank(C n k) : const ⊤ ⇉ BT(C n k) (const ⊤)
\end{code}
The base and inductive cases of |ImmediateSublistInduction| fit into these |Fam'| categories too: given |a : Set| and |s : ∀ {k} → Fam (Vec k a)|, I can write
\begin{code}
g  : BT(C sk k) s  ⇉' s
e  : const ⊤       ⇉' s {0}
\end{code}
(It's important to say explicitly that the target of~|e| is |s {0} : Fam (Vec 0 a)| to make it clear that |e|~gives a solution for the empty list.)

\pause

I haven't done much really.
It's just a bit of abstraction that hides part of the indices, and might even be described as cosmetic.
What's important is that, by fitting my programs into the |Fam'| categories, I can start talking about them in the categorical language.
In particular, I want to talk about naturality.
That means I should look for \emph{functors} and \emph{natural transformations} in my programs.

A parametric data type such as |BT_ n k| is categorically the object part of a \emph{functor}, which maps objects in a category to objects in a possibly different category.
In the case of |BT_ n k|, the functor goes from |Fam' (Vec k a)| to |Fam' (Vec n a)| --- indeed I can rewrite the type of |BT_ n k| as
\begin{code}
BT_ n k : Fam (Vec k a) → Fam (Vec n a)
\end{code}
The |BT|-typed trees are made up of the constructors of |BT| and hold elements of types~|p|.
A categorical insight is that the constructors constitute an \emph{independent} layer of data added by the functor outside the elements.
The independence of this functor layer is described formally by the definitions of functors and natural transformations.

One aspect of the independence is that the functor layer can stay the same and impervious to whatever is happening at the inner layer.
Categorically, `whatever is happening' means an arbitrary morphism.
In the case of |BT|, the inner layer (the elements) may be changed by some arbitrary morphism of type |p ⇉ q|, and that can always be lifted to a morphism of type |BT_ n k p ⇉ (BT_ n k) q| that doesn't change the functor layer (the tree constructors).
This lifting is the morphism part of a functor, and is the map function that comes with any (normal) parametric data type.
I've already had a map function for |BT|, and indeed its type can be rewritten as
\begin{code}
mapBT : (p ⇉ q) → ((BT_ n k) p ⇉ (BT_ n k) q)
\end{code}
In a sense, a lifted morphism such as |mapBT f| is essentially just~|f| since |mapBT f| does nothing to the functor layer, so when |f|~is a composition, that composition shows up at the level of lifted morphisms too.
Formally, this is stated as a \emph{functoriality} equation:
\begin{code}
mapBT (f' · f) = mapBT f' · mapBT f
\end{code}
(Also |mapBT id =' id| in the extreme case of composing no morphisms.)

The functor layer may also be changed by \emph{natural transformations} independently of whatever is happening at the inner layer.
In |Fam'| categories, a natural transformation has type |∀ {p} → F p ⇉ G p| for some functors |F|~and~|G|, and transforms an |F|-layer to a |G|-layer without changing the inner layer~|p|, whatever |p|~is.
For example, |retabulate| transforms the functor layer |BT_ n k| to a \emph{composition} of functors |BT_ n sk · (BT_ sk k)| (which can be regarded as two functor layers) without changing~|p|.
(Indeed, |retabulate| transforms only the tree constructors and doesn't change the elements to something else.)
Moreover, this transformation of the functor layer is not interfered by whatever is happening at the inner layer.
Again `whatever is happening' amounts to a quantification over all morphisms: for any |f : p ⇉ q| happening at the inner layer, if |retabulate| is happening at the functor layer too, it doesn't make a difference whether |f|~or |retabulate| happens first, because they happen at independent layers.
Formally, this is stated as a \emph{naturality} equation (where |f|~needs to be lifted appropriately):
\begin{code}
retabulate · mapBT f = mapBT (mapBT f) · retabulate
\end{code}

%\todo[inline]{Revise these to highlight the diagrammatic intuition about layer independence, which is already discussed in the previous section.}

%\todo[inline]{Richard already pointed out that naturality is the key; try string diagrams!}

\pause

With functor composition, in general there can be many functor layers in an object (like the target of |retabulate|), and all these layers can be transformed independently by natural transformations.
The best way of managing this structure is to use \emph{string diagrams}.
In string diagrams, functors are drawn as wires, and natural transformations are drawn as dots with input functors/wires attached below and output functors/wires above.
(I learned string diagrams mainly from \citet{Coecke-PQP}, so my string diagrams have inputs below and outputs on top.
I'm also thinking about giving \varcitet{Hinze-string-diagrams}{'s} new textbook a try.)
The natural transformations I've got are |retabulate| and |unTip|, and I can draw their types as
\[ \tikzfig{pics/retabulate-unTip} \]
String diagrams focus on the functor layers and represent them explicitly as a bunch of wires --- functor composition is represented as juxtaposition of wires, and the identity functor is omitted (since it's the composition of no functors).
Drawn as a string diagram, |retabulate| has one input wire labelled |BT_ n k| and two output wires |BT_ n sk| and |BT_ sk k|, since it transforms a |BT_ n k| layer to two layers |BT_ n sk · (BT_ sk k)|.
The diagram of |unTip| goes from one wire to none, since |unTip| transforms |BT_ n n| to the identity functor.
(Indeed, what |unTip| does is get rid of the |tipZ| or |tipS| constructor.)

Whereas functor composition spreads horizontally, sequential composition of natural transformations goes vertically.
Given transformations |α : ∀ {p} → F p ⇉ G p| and |β : ∀ {p} → G p ⇉ H p|, their sequential composition |β ∘ α : ∀ {p} → F p ⇉ H p| is drawn in a string diagram as |α|~and~|β| juxtaposed vertically and sharing the middle wire with label~|G| (obscuring a section of the wire):
\[ \tikzfig{pics/vertical} \]

The power of string diagrams becomes evident when things happen in both the horizontal and vertical dimensions.
For example, suppose there are two layers |F|~and~|F'|, where the outer layer~|F| should be transformed by~|α| and the inner layer~|F'| by |α' : ∀ {p} → F' p ⇉ G' p|.
There are two ways of doing this: either |map(sub G) α' ∘ α|, where the outer layer~|F| is transformed to~|G| first, or |α ∘ map(sub F) α'|, where the inner layer~|F'| is transformed to~|G'| first.
The two ways can be proved equal using the naturality of~|α|, but the equality can be seen more directly with string diagrams:
\[ \tikzfig{pics/horizontal-definitions} \]
The |map| means skipping over the outer/left functor and transforming the inner/right functor; so in the diagrams, |α'|~is applied to the inner/right wire.
(The dashed lines are added to emphasise that both diagrams are constructed as the sequential composition of two transformations.)
By placing layers of functors in a separate dimension, it's much easier to see which layers are being transformed, and determine whether two sequentially composed transformations are in fact applied independently, so that their order of application can be swapped.
This is abstracted as a diagrammatic reasoning principle: dots in a diagram can be moved upwards or downwards, possibly changing their vertical positions relative to other dots (while stretching or shrinking the wires, which can be thought of as elastic strings), and the (extensional) meaning of the diagram will remain the same.

\pause

I want to draw the two algorithms as string diagrams.
However, some of their components, namely |blank|, |e|, and~|g|, are not natural transformations.
Technically, only natural transformations can go into string diagrams.
But I'm still tempted to draw those components intuitively as
\[ \tikzfig{pics/blank-g-e} \]
After a bit of thought, I come up with some technical justification.
Any morphism |f : p ⇉ q| can be lifted to have the type |∀ {r} → (const p) r ⇉ (const q) r|, and become a natural transformation from |const p| to |const q|.
It's fine to leave the lifting implicit and just write |p|~and~|q| for wire labels, since it's usually clear that |p|~and~|q| are not functors and need to be lifted.
For example, |s|~is a type family, which is an object in a |Fam'| category, and needs to be lifted to |const s| to be a functor.
For~|⊤| there's one more step: |⊤|~abbreviates the type family |const ⊤|, which is an object in a |Fam'| category, and needs to be further lifted to |const (const ⊤)| to be a functor.
It's kind of technical, but in the end these diagrams are okay.

%With this lifting, the usual naturality can also be reformulated diagrammatically:
%For any |f : a → b|,
%\[ |map(sub G) f ∘ α = α ∘ map(sub F) f| \hspace{.15\textwidth} \tikzfig{pics/naturality} \]
%The reformulation makes it intuitively clear that the naturality of~|α| is about |α|~transforming only the outer functor, independently of whatever is happening inside.

%\todo[inline]{Recap of string diagrams for 2-categories, i.e., layered type structure (composition of functors); layers may be transformed independently of others, and this intuition is captured by the definition of natural transformations.
%The two sides of a traditional naturality equation look rather different, whereas in a diagrammatic equation the two sides are `the same picture', allowing us to change perspectives effortlessly.}

\subsection{Diagrammatic Reasoning}

All the abstract nonsense took me some time.
But I still don't know whether string diagrams will actually help me to understand the two algorithms from \cref{sec:equality-from-types}.
It's time to find out.

I'm not confident enough to work with the recursive definitions straight away, so I take the special case |td s e g 3| of the top-down algorithm and unfold it into a deeply nested expression involving |mapBT|s and |blank|s (as on the left of \cref{fig:td-diagram}).
Transcribing that into a string diagram is basically writing down all the intermediate type information and laying out the layered type structures horizontally~(as on the right of \cref{fig:td-diagram}). For example, the rightmost component |blank(C 3 2)| in the expression has type |const ⊤ ⇉ BT(C n k) (const ⊤)|, which ---~after eliding the |const|s, as I've just decided to do~--- is drawn as the bottom Y-junction in the string diagram. \Jeremy{How's this? Do you think of it as a ``Y-junction''? A ``fork''?
% ``Recall that |s| here is a type family, an object in this category, so is drawn as a wire label, whereas |e| and |g| are natural transformations, so drawn as dots.'' Worth saying? Josh: I didn't see this comment was about the |td| diagram. We've just seen the string-diagrammatic definitions of |blank|, |g|, and~|e|, so maybe the info needed here is how to get from those definitions to this diagram?
}

\begin{figure}
\begin{center}
\begin{varwidth}{\textwidth}
\setlength{\mathindent}{0em}
\begin{code}
td s e g 3 =  g ∘
              mapBT  (  g ∘
                        mapBT  (  g ∘
                                  mapBT e ∘
                                  blank(C 1 0)) ∘
                        blank(C 2 1)) ∘
              blank(C 3 2)
\end{code}
\end{varwidth}%
\hspace{.1\textwidth}%
\begin{varwidth}{\textwidth}
\ctikzfig{pics/td}
\end{varwidth}
\end{center}
\caption{A special case of the top-down algorithm as a string diagram.}
\label{fig:td-diagram}
\end{figure}

All the |mapBT|s are gone in the diagram, because I can directly apply a transformation to the intended layers/wires, rather than count awkwardly how many outer layers I have to skip using |mapBT|, one layer at a time.
Functoriality is also transparent in the diagram, so it's slightly easier to see that |td| has two phases (between which I draw a dashed line): the first phase constructs deeply nested blank tables, and the second phase fills and demolishes the tables inside out.

Functoriality is already somewhat transparent in the traditional expression though, thanks to the infix notation of function composition.
So I suppose I don't absolutely need the string diagram to see that |td| has two phases, although the required rewriting~(\cref{fig:functoriality-rewriting}) is not as trivial as just seeing the two phases in the diagram.
Moreover, there's nothing I can meaningfully move in the diagram --- all the transformations here are lifted after all.

\begin{figure}
\begin{center}
\begin{code}
  td s e g 3
=   {-\;definition -}
  g ∘ mapBT (g ∘ mapBT (g ∘ mapBT e ∘ blank(C 1 0)) ∘ blank(C 2 1)) ∘ blank(C 3 2)
=   {-\;functoriality -}
  g ∘ mapBT (g ∘ mapBT (g ∘ mapBT e) ∘ mapBT blank(C 1 0) ∘ blank(C 2 1)) ∘ blank(C 3 2)
=   {-\;functoriality -}
  g ∘ mapBT (g ∘ mapBT (g ∘ mapBT e)) ∘
  mapBT (mapBT blank(C 1 0) ∘ blank(C 2 1)) ∘ blank(C 3 2)
\end{code}
\end{center}
\caption{Rewriting |td s e g 3| into two phases using functoriality.}
\label{fig:functoriality-rewriting}
\end{figure}

Hm. Maybe I'll have more luck with the bottom-up algorithm, which has `real' natural transformations?
I go on to expand |bu s e g 3|.
The loop in the expression unfolds into a sequence of functions, alternating between |retabulate| and |mapBT g|.

`A sequence\ldots'
I mutter.
I didn't expect anything else from unfolding a loop. But the sequential structure is so different from the deeply nested structure of |td|.

And then, something unexpected yet familiar appears in the transcribed diagram~(\cref{fig:bu-diagram}).

\begin{figure}
\begin{center}
\begin{varwidth}{\textwidth}
\setlength{\mathindent}{0em}
\begin{code}
bu s e g 3 =  unTip ∘

                mapBT g     ∘
                retabulate  ∘

                mapBT g     ∘
                retabulate  ∘

                mapBT g     ∘
                retabulate  ∘

              mapBT e ∘
              blank(C 3 0)
\end{code}
\end{varwidth}%
\hspace{.1\textwidth}%
\begin{varwidth}{\textwidth}
\ctikzfig{pics/bu}
\end{varwidth}
\end{center}
\caption{A special case of the bottom-up algorithm as a string diagram.}
\label{fig:bu-diagram}
\end{figure}

\begin{aha}
There are also two phases for table construction and demolition, and the |g|s and |e| in the demolition phase are \emph{exactly the same} as in |td|!
\end{aha}

The string diagram is truly helpful this time.
Now I see, as Richard hinted, that I could rewrite the traditional expression using the naturality of |unTip| and |retabulate| to push |g|~and~|e| to the left of the sequence and separate the two phases~(\cref{fig:naturality-rewriting}).
But in the string diagram, all those rewritings amount to nothing more than gently pulling the two phases apart, eventually making the dashed line horizontal.
In fact I don't even bother to pull, because on this diagram I can already see simultaneously both the sequence (the dots appearing one by one vertically) and the result of rewriting the sequence using naturality.

\begin{figure}
\begin{center}
\setlength{\mathindent}{0em}
\begin{code}
   bu s e g 3
=  {-\;definition -}
   unTip ∘ mapBT g ∘ retabulate ∘ mapBT g ∘ retabulate ∘ mapBT g ∘ retabulate ∘ mapBT e ∘ blank(C 3 0)
=  {-\;naturality of |unTip| -}
   g ∘
   unTip ∘ retabulate ∘ mapBT g ∘ retabulate ∘ mapBT g ∘ retabulate ∘ mapBT e ∘ blank(C 3 0)
=  {-\;naturality of |retabulate| -}
   g ∘
   unTip ∘ mapBT (mapBT g) ∘ retabulate ∘ retabulate ∘ mapBT g ∘ retabulate ∘ mapBT e ∘ blank(C 3 0)
=  {-\;naturality of |unTip| again -}
   g ∘ mapBT g ∘
   unTip ∘ retabulate ∘ retabulate ∘ mapBT g ∘ retabulate ∘ mapBT e ∘ blank(C 3 0)
=  {-\;similarly -}
   g ∘ mapBT g ∘ mapBT (mapBT g) ∘ mapBT (mapBT (mapBT e)) ∘
   unTip ∘ retabulate ∘ retabulate ∘ retabulate ∘ blank(C 3 0)
=  {-\;functoriality -}
   g ∘ mapBT (g ∘ mapBT (g ∘ mapBT e)) ∘
   unTip ∘ retabulate ∘ retabulate ∘ retabulate ∘ blank(C 3 0)
\end{code}
\end{center}
\caption{Rewriting |bu s e g 3| into two phases using naturality.}
\label{fig:naturality-rewriting}
\end{figure}

%\todo[inline]{Specialised cases (with a concrete size) only; production and consumption parts, which can be separated by naturality.}

\pause

So, modulo naturality, the two algorithms have the same table demolition phase but different table construction phases.
If I can prove that their table construction phases are equal, then I'll have another proof that the two algorithms are equal, in addition to the parametricity-based proof~(\cref{sec:equality-from-types}).
For |td|, the construction phase is a right-leaning tree on the diagram, whereas for |bu| it's a left-leaning tree.
Maybe what I need is an equation about |blank| and |retabulate| that can help me to rotate a tree\ldots?
%
\[ \text{\lstinline{cd (choose k xs)}} \equals \text{\lstinline{mapB (flatten . choose k) (choose (k+1) xs)}} \]

The equation~\cref{eq:cd-spec} flashes through my mind.
Of course it has to be this equation --- I used it as a specification for \lstinline{cd}, the Haskell predecessor of |retabulate|.
How else would I introduce |retabulate| into the picture?
But first let me update this for my dependently typed string diagrams:
%\todo{No need for \lstinline{flatten}}
\begin{equation}
\tikzfig{pics/rotation}
\tag{$\ast\ast$}
\label{eq:rotation}
\end{equation}
That's a tree rotation all right!
So I should do an induction that uses this equation to rotate the right-leaning tree in |td| and obtain the left-leaning tree in |bu|~(\cref{fig:rotations}).
And then I'll need to prove the equation, meaning that I'll need to go through the definitions of |retabulate| and |blank|\ldots
Oh hell, that's a lot of work.

\begin{figure}
\ctikzfig{pics/rotations}
\caption{Rewriting the table construction phase of |td s e g 3| to that of |bu s e g 3| using the |rotation| equation~\cref{eq:rotation}.}
\label{fig:rotations}
\end{figure}

%\todo[inline]{To prove the equality between |td| and |bu| along this direction:
%The consumption parts of the two algorithms are the same.
%The production parts are left- and right-leaning trees; use the |retabulate|-|blank| equation (\lstinline{cd}–\lstinline{choose} in Haskell), which is diagrammatically some kind of rotation?
%(Looks like co-associativity; maybe |BT| is some kind of graded comonad?)
%The rotation proof is not difficult but not trivial either, and the |retabulate|-|blank| equation still needs to be established by delving into the definitions\ldots}

\begin{aha}
But wait a minute~--- do I really need to go through all this?
\end{aha}

The three functors at the top of the diagrams~\cref{eq:rotation} catch my attention.
In Agda, they expand to the type |BT(C n sk) (BT(C sk k) (const ⊤)) xs|.
An inhabitant of this type is a table of \emph{blank} tables, so there is no choice of table entries;
and moreover the structures of all the tables are completely determined by the indices\ldots the type has a unique inhabitant!
So the equation is actually trivial to prove, because, forced by the type, the two sides have to construct the same table, and I don't need to look into the definitions of |retabulate| and |blank|!

Relieved, I start to work on the proof.
The precise notion I need here is (mere) propositions~\citep[Chapter~3]{UFP-HoTT}:
\begin{code}
isProp : Set → Set
isProp a = {x y : a} → x ≡ y
\end{code}
The type |BT(C n k) p xs| is propositional if the element types~|p| are propositional --- this is easy to prove by a straightforward double induction:
\begin{code}
BT-isProp : (∀ {ys} → isProp (p ys)) → isProp (BT(C n k) p xs)
\end{code}
And then the equation~\cref{eq:rotation} can be proved trivially by invoking |BT-isProp| twice:
\begin{code}
rotation : retabulate (blank(C n k) tt) ≡ mapBT blank(C sk k) (blank(C n sk) tt)
rotation = BT-isProp (BT-isProp refl)
\end{code}
The side conditions of |retabulate| and |blank| (omitted above) are all universally quantified.
Usually they make proofs more complex, but not in this case because the proof doesn't look into any of the function definitions.
As long as the type is blank nested tables, the two sides of an equation can be arbitrarily complicated, and I can still prove them equal just by using |BT-isProp|.

\begin{aha}
Wait, blank nested tables --- aren't those what the construction phases of both algorithms produce?
\end{aha}

\Josh{Bad spacing after aha}
I face-palm.
It was a waste of time proving the |rotation| equation.
The construction phases of both algorithms produce blank nested tables of the same type --- |BT(C 3 2) (BT(C 2 1) (BT(C 1 0) (const ⊤))) xs| in the concrete examples I tried (\cref{fig:td-diagram,fig:bu-diagram}).
So I can directly prove them equal using |BT-isProp| three times.
There's no need to do any rotation.

%\todo[inline]{Second climax: the types have already proved the equality between the production parts for us!}

Oh well, |rotation| is still interesting because it helps to explain how the two algorithms are related intensionally: they produce the same layers of tables but in opposite orders, and |rotation| helps to show how one order can be rewritten into the other~(\cref{fig:rotations}).
It's just that a |rotation|-based proof would be quite tedious, and I don't want to go through with that.
A proof based on |BT-isProp| should be much simpler.
Conceptually I've figured it all out: both algorithms have two phases modulo naturality; their table demolition phases are exactly the same, and their table construction phases are equal due to the |BT-isProp| reasoning.
But the general proof is still going to take some work.
If I want to stick to string diagrams, I'll need to transcribe the algorithms into inductively defined diagrams.
Moreover, the |BT-isProp| reasoning is formally an induction (on the length of the input list), which needs to be worked out.
And actually, compared with a diagrammatic but unformalised proof, I prefer a full Agda formalisation.
That means I'll need to spell out a lot of detail, including functoriality and naturality rewriting~(\cref{fig:functoriality-rewriting,fig:naturality-rewriting}).
Whining, I finish the entire proof in Agda.
But as usual, in the end there's a dopamine hit from seeing everything checked.

%\todo[inline]{Sketch inductive diagrammatic definitions and Agda formalisation}

\pause

Still, I can't help feeling that I’ve neglected a fundamental aspect of the problem: why the bottom-up algorithm is more efficient.
After making all the effort adopting dependent types and string diagrams, do these state-of-the-art languages help me say something about efficiency too?

String diagrams make it easier for me to see that the table construction phases of both algorithms produce the same layers of tables but in opposite orders.
Only the order used by the bottom-up algorithm allows table construction and demolition to be interleaved, and consequently the algorithm keeps no more than two layers of tables at any time.
That's the crucial difference between the two algorithms.
Now I need to figure out what the difference means algorithmically.

More specifically, why is it good to keep \emph{two} layers of tables and not more?

When there are multiple layers of tables of type |BT(C n k)| with |k < n|, meaning that the input list is split into proper sublists multiple times, all the final sublists will appear (as indices in the element types) in the entire nested table multiple times --- that is, overlapping subproblems will appear.
Therefore, when I use~|g| to fill in a nested table, I'm invoking~|g| to compute solutions for overlapping subproblems repetitively, which is what I want to avoid.
More precisely, `using~|g| to fill in a nested table' means applying~|g| under at least two layers, for example |mapBT (mapBT g) : BT(C 3 2) (BT(C 2 1) (BT(C 1 0) s)) ⇉ BT(C 3 2) (BT(C 2 1) s)|, where the result is at least two layers of tables, so there should be at least \emph{three} layers of tables (to which |mapBT (mapBT g)| is applied) for overlapping subproblems to be solved repetitively.
The bottom-up algorithm never gets to three layers of tables, and therefore avoids solving overlapping subproblems.

That reasoning doesn't sound too bad, although it's clear that there's much more to be done.
The whole argument is still too informal and lacks detail.
It's easy to poke holes in the reasoning --- for example, if the input list has duplicate elements, then the bottom-up algorithm won't be able to entirely avoid solving overlapping subproblems repetitively.
To fix this, the algorithm will need a redesign.
And of course it's tempting to explore more problem-decomposing strategies other than immediate sublists.
Eventually I may arrive at something general about dynamic programming, which was what Richard wanted to work out in his paper.

All those are for another day, however.
I've had enough fun today.
Mostly, what I did was transcribe programs into new languages, but that helped me to reason in new ways, using more convenient tools to tackle Richard's problem.

I wish Richard was still around so that I could show all these to him.
He would've liked the new languages and the new ways of reasoning.

%\todo[inline]{How about dedicating this story to Richard by ending with something like: `I wish Richard was still around so that I could show all these to him. He would've liked the new languages and the new ways of thinking.' Also implicitly explains why Richard's been referred to by his first name. JG: lovely!}

%\todo[inline]{Algorithmically:
%The production parts build the same nested tables but in different orders, and the order used by bottom-up algorithm allows production and consumption to be interleaved.
%Overlapping subproblems occur in two layers of tables, and they are solved repetitively when |g|~is used to produce two or more layers of tables, which is what the top-down algorithm does after creating deeply nested tables.
%The bottom-up algorithm avoids the repetitive computation because it always uses~|g| to produce only one layer of table.
%(Two layers of tables only appear due to |retabulate|, which only duplicates and redistributes already computed solutions and doesn't recompute them.)}

\section*{Afterword}

We have presented this work as a kind of `Socratic monologue', recording in an intuitive and colloquial style the thought processes of a dependently typed programmer as they solve a programming mystery. We were inspired by the opening chapters of the science fiction novel \textit{Project Hail Mary} by Andy Weir. 

We have chosen this style over the traditional rational reconstruction of a finished piece of work. We hope that the reader finds the format effective for focusing on the main ideas while going through a development; after all, we don't usually hurry to work out all the technical details when first solving a problem. Our telling largely follows our actual development, going from the concrete to the abstract: ``based on a true story''. 

We have resisted the temptation to generalise ---~for example, to dynamic programming more broadly, as \citet{Bird-zippy-tabulations} attempted to do. We have kept the material as simple as possible, avoiding a digression into graded comonads. We have also kept it fairly self-contained; but we have not written a detailed tutorial, nor explained Agda from scratch or given formal categorical definitions. We have left a few loose ends here and there to point out possible extensions and future exercises and papers.

\todo[inline]{Compare with \varcitet{Mu-sublists}{'s} treatment of the problem using simple types and equational reasoning}

We believe that dependent types, category theory, and string diagrams should be in the (mathematically inclined) functional programmer's toolbox. 
We can discover, explain, and prove things by writing them down in the appropriate language.
Fancy types can replace traditional specifications and proofs (for example, equality between programs can be proved simply by showing that they have the same, uniquely inhabited type), and going beyond length/shape indexing is still an under-explored methodology.
Likewise, category theory offers useful abstractions, such as for comprehending indexed definitions as if they were simply typed; in particular, the categorical abstraction enables the use of string diagrams to make reasoning with naturality transparent (and in this case the main proof is entirely about naturality, and is rendered trivial).

\begin{acks}
% omitted automatically in anonymous mode
\todo[inline]{We'll eventually need acknowledgements. This is a placeholder to remember to thank Julie Summers, Royal Literary Fund Fellow at Kellogg College.}
\todo[inline]{Liang-Ting offered some helpful suggestions too.}
\end{acks}

\bibliographystyle{ACM-Reference-Format}
\bibliography{bib}

\end{document}
