\documentclass[acmsmall,fleqn,screen,review]{acmart}

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

\usepackage{mathtools}

\usepackage{listings}
\lstset{basicstyle=\ttfamily, basewidth=0.5em, xleftmargin=2\parindent, morekeywords={data, where}}

\usepackage{mdframed}
\newenvironment{temp}{\begin{mdframed}[backgroundcolor=red!7, linewidth=0, skipabove=1ex, leftmargin=1ex, rightmargin=0, innerleftmargin=0, innerrightmargin=0, innertopmargin=0, innerbottommargin=0]}{\end{mdframed}}
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

\newcommand{\equals}{\enskip=\enskip}

\usepackage{tikzit}
\input{string.tikzstyles}

\let\Bbbk\relax
%include agda.fmt

\definecolor{suppressed}{RGB}{225,225,225}
\definecolor{goal}{RGB}{209,243,205}
\newcommand{\highlight}[2]{\smash{\text{\colorbox{#1}{\kern-.1em\vphantom{\vrule height 1.2ex depth 0.1ex}\smash{\ensuremath{#2}}\kern-.1em}}}}

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
%format CHOOSE (n) (k) = "C^{" n "}_{" k "}"

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
%format _∷_ = _ ∷ _
%format ∷_ = ∷ _
%format ᴮᵀ = "_{\Conid{BT}}"
%format ∷ᴮᵀ = ∷ ᴮᵀ
%format _∷ᴮᵀ_ = _ ∷ᴮᵀ _
%format _∷ᴮᵀ = _ ∷ᴮᵀ
%format > = "\unskip>\ignorenext"
%format GEQ = "\unskip\ge\ignorenext"
%format ≤ = "\unskip\le\ignorenext"
%format _≤_ = _ "{\le}" _
%format < = "\unskip<\ignorenext"
%format ≤↑ = "\unskip\mathrel{\le_\uparrow}\ignorenext"
%format _≤↑_ = _ "{\le_\uparrow}" _
%format ↓≤ = "\unskip\mathrel{_\downarrow\kern-.8pt{\le}}\ignorenext"
%format _↓≤_ = _ "{_\downarrow\kern-.8pt{\le}}" _
%format ↓≤' = "{_\downarrow\kern-.8pt{\le}}"
%format CDOTS = "\cdots"

%format B' = B "^\prime"
%format (B'_(n)(k)) = B' "{}^{" n "}_{" k "}"
%format testB' = test B'
%format (BT_(n)(k)) = BT "^{" n "}_{" k "}"
%format mapBT = map ᴮᵀ
%format zipBTWith = zip ᴮᵀ "\kern-1pt" With
%format blanks' = blanks "^\prime"
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
%format s = "\Var s"
%format t = "\Var t"
%format u = "\Var u"
%format v = "\Var v"
%format x = "\Var x"
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
%format sk = 1 + k
%format ssk = 2 + k

%format n>k = n "{>}" k
%format nGEQk = n "{\geq}" k
%format skGEQk = sk "{\geq}" k
%format nGEQsk = n "{\geq}" sk

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
\todo[inline]{Abstract: a demonstration of dependent types and string diagrams for the functional programmer (ideally already with a bit exposure to dependent types and category theory and not put off by basic concepts like indexed types, functors, and so on)}
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

\todo[inline]{Including the sections to see the overall structure; may consider omitting the sections altogether when the manuscript is finished}

\tableofcontents

\section{Teaser}

`What on earth is this function doing?'

I stare at the late Richard Bird's `Zippy Tabulations of Recursive Functions'~\citeyearpar{Bird-zippy-tabulations}, frowning.

\begin{lstlisting}
cd                        :: B a -> B (L a)
cd (Bin (Tip x) (Tip y))  =  Tip [x, y]
cd (Bin t (Tip y))        =  Bin (cd t) (mapB (: [y]) t)
cd (Bin (Tip y) u)        =  Tip (y : ys) where Tip ys = cd u
cd (Bin t u)              =  Bin (cd t) (zipBWith (:) t (cd u))
\end{lstlisting}

I know \lstinline{B} is this Haskell datatype of trees,
\begin{lstlisting}
data B a = Tip a || Bin (B a) (B a)
\end{lstlisting}
And presumably \lstinline{mapB} and \lstinline{zipBWith} are the usual \lstinline{map} and \lstinline{zipWith} functions for these trees, and \lstinline{L} is the standard data type of lists.
But how did Richard come up with such an incomprehensible function definition?
%\Jeremy{We should be more consistent about whether to call him Richard or Bird. Shin: does it work if we say "Richard" when we refer to the person and say Bird (2008) when we refer to the paper?}
He didn't bother to explain it in the paper.

\section{Simply Typed Algorithms}

From the explanations that \emph{are} in the paper, I can make a pretty good guess at what \lstinline{cd} is doing at a high level.
%
\citet{Bird-zippy-tabulations} is studying the relationship between top-down and bottom-up algorithms. A generic top-down algorithm is specified by:%
\todo{Make the function polymorphic}
%\Josh{Include |f| and |g| as arguments (like |foldr| etc). Shin: Done.}
%\Jeremy{Can we avoid using \lstinline{$}? Richard wouldn't have used it\ldots. Shin: Used application instead.}
\begin{lstlisting}
td :: (a -> b) -> (L b -> b) -> L a -> b
td f g [x] = f x
td f g xs  = g (map (td f g) (dc xs))
\end{lstlisting}
The input of \lstinline{td} is a list of \lstinline{a}'s, and the output is a single value of type \lstinline{b}.
Singleton lists form the base cases, processed by a function \lstinline{f}.
A non-singleton list is decomposed into shorter lists by \lstinline{dc :: L a -> L (L a)}.
Each shorter list is then recursively processed by \lstinline{td}, before \lstinline{g} combines the results.%
%\Josh{\lstinline{F} is initially \lstinline{L} and later \lstinline{B}, but this changes the type of \lstinline{g} too (no need for \lstinline{cvt} etc)? Shin: removed \lstinline{F}. I think we still need \lstinline{cvt} after switching to \lstinline{B}.}
\footnote{The setting in \citet{Bird-zippy-tabulations} is more general: \lstinline{L} need not be a list, and \lstinline{dc} returns an \lstinline{F}-structure of lists. We simplified the setting for ease of discussion.}

\begin{figure}[t]
\centering
\includegraphics[width=0.5\textwidth]{pics/td-call-tree.pdf}
\caption{Computing \lstinline{td "abcd"} top-down.}
\label{fig:td-call-tree}
\end{figure}

In the last (and the most difficult) example in the paper,
\lstinline{dc :: L a -> L (L a)}
%\Josh{Give definition, which is generalised to \lstinline{choose} later? Shin: done.}
computes all the \emph{immediate sublists} of the given list --- all the lists with exactly one element missing:
\begin{lstlisting}
dc [x,y]       = [[x],[y]]
dc (xs ++ [x]) = [xs] ++ [ys ++ [x] || ys <- dc xs]
\end{lstlisting}
(This assumes that a list can be matched with a snoc pattern \lstinline{xs ++ [x]}.)
To compute \lstinline{td "abcd"}, for example, we need to compute \lstinline{td "abc"}, \lstinline{td "abd"}, \lstinline{td "acd"}, and \lstinline{td "bcd"}, as seen in \cref{fig:td-call-tree}.
To compute \lstinline{td "abc"} in turn, we need \lstinline{td "ab"}, \lstinline{td "ac"}, and \lstinline{td "bc"}.
Notice, however, that \lstinline{td "ab"} is invoked again when computing \lstinline{td "abd"}:
following this top-down computation, many sub-computations are repeated.

\begin{figure}[t]
\centering
\includegraphics[width=0.43\textwidth]{pics/sublists-lattice.pdf}
\caption{Computing \lstinline{td "abcd"} bottom-up.
To save space we omitted the \lstinline{td}s.}
\label{fig:sublists-lattice}
\end{figure}

It is better to proceed bottom-up instead, as depicted in Figure~\ref{fig:sublists-lattice}.%
\Josh{Maybe add a greyed-out 0-th level.}
The $n$-th level consists of values of \lstinline{td} at lists of length~$n$.
We start from level~$1$, and compute level $n+1$ from level~$n$ by reusing the values stored in the latter, until we reach the top level consisting of only one value.
If the levels are lists, level~$2$ will be
\begin{lstlisting}
  [td "ab", td "ac", td "bc", td "ad" ...]
\end{lstlisting}
To construct level~$3$ from level~$2$, we need a function \lstinline{cd :: L a -> L (L a)} that, given level~$2$, copies and rearranges its elements such that the result of \lstinline{td} at immediate sublists of the same list are brought together:
\begin{lstlisting}
  [[td "ab", td "ac", td "bc"], [td "ab", td "ad", td "bd"] ... ]
\end{lstlisting}
Applying \lstinline{map g} to the list above, we get level $3$:
\begin{lstlisting}
  [td "abc", td "abd", td "acd", td "bcd" ...]
\end{lstlisting}
If such a function \lstinline{cd} can be constructed, a bottom-up algorithm computing the same value as \lstinline{td} is given by:%
%\Josh{Bring \lstinline{head} in front of \lstinline{loop}? Shin: Done.}
%\Jeremy{Unless we're really pressed for space, I think it is better to put this on four lines. Shin: Done.}
\begin{lstlisting}
bu :: (a -> b) -> (L b -> b) -> L a -> b
bu f g = head . loop . map f
  where
    loop [y] = [y]
    loop ys  = loop (map g (cd ys))
\end{lstlisting}
That is, level $1$ is obtained by applying \lstinline{f} to each element of the input list. Then we keep applying \lstinline{map g . cd} to get the next level, stopping when we get a level with a single element, which will be our result.

The \lstinline{bu} given above is much simpler than Richard's: to cope with more general problems, he had to store not just values but tables of values in each level.
I'm puzzled at first by why Richard starts from singleton lists instead of the empty list (missing the bottom of the lattice). But then I realise that whereas a $2$-list is completely determined by its two $1$-element sublists, a $1$-list is not determined by its one $0$-element sublist~--- more context would be needed.
%\Jeremy{\ldots but in Agda, this context can be provided in the type.}

All these, however, are merely a first attempt.
Richard must have realised at some point that it is difficult to define the \lstinline{cd} rearrangement using lists, and decided to represent each level using the \lstinline{B} datatype mentioned before.
%\Josh{Do we get any explanation from the dependently typed reformulation? (Easy access to particular groups of sub-lists?)}
Now \lstinline{cd} has type \lstinline{L a -> B (L a)}, and \lstinline{bu} and \lstinline{loop} are defined by
\begin{lstlisting}
bu :: (a -> b) -> (L b -> b) -> L a -> b
bu f g = unTip . loop . cvt . map f
  where
    loop (Tip y) = Tip y
    loop ys      = loop (mapB g (cd ys))
\end{lstlisting}
where \lstinline{loop} has type \lstinline{B b -> B b}, and \lstinline{unTip (Tip y) = y}.
The function \lstinline{cvt :: L a -> B a} prepares the first level.
%\Josh{A point of comparison (later we don't need this conversion)}

\begin{figure}[t]
\centering
\includegraphics[width=0.8\textwidth]{pics/map_g_cd.pdf}
\caption{How \lstinline{mapB g . cd} constructs a new level.
Again, \lstinline{ab}, \lstinline{ac}... etc. denote results of \lstinline{td}, not the sublists themselves.}
\label{fig:map_g_cd}
\end{figure}

I try to trace Richard's \lstinline{cd} to find out how it works.
Given input \lstinline{"abcde"}, the function \lstinline{cvt} yields a tree that is slanted to the left as level $1$:
%\Josh{Wrong order? Shin: Richard's \lstinline{cvt} is \lstinline{foldl1 Bin . map Tip}.. so it is his order. If that's not consistant with ours... let's think about what to do. :(}
\begin{lstlisting}
Bin (Bin (Bin (Bin (Tip 'a') (Tip 'b')) (Tip 'c')) (Tip 'd')) (Tip 'e')
\end{lstlisting}
Following Richard's convention, I draw a \lstinline{Tip x} as \lstinline{x}, and draw \lstinline{Bin t u} as a dot with \lstinline{t} to its left and \lstinline{u} below, resulting in the tree labelled (1)
in Figure~\ref{fig:map_g_cd}.
Applying \lstinline{mapB g . cd} to this, I get level $2$, labelled (2) in the figure.
For a closer look, I apply \lstinline{cd} to level $2$.
Indeed, with its clever mapping and zipping, \lstinline{cd} managed to bring together precisely the right elements (labelled (2.5) in Figure~\ref{fig:map_g_cd}), so that when we apply \lstinline{mapB g}, we get level $3$.
\Shin{I added the second sentence in the caption of Figure~\ref{fig:map_g_cd}. I think it's probably necessary because I myself got confused from time to time.}
\Josh{Should update this paragraph and \cref{fig:map_g_cd} for just \lstinline{"abcd"}.
SCM: But I think we need an input with 5 elements to see more structure in the tree. I'd rather update previous examples to \lstinline{"abcde"} if we have to...
It's probably too much to use \lstinline{"abcde"} in S3, however.}

This still does not give me much intuition for why \lstinline{cd} works.
Presumably \lstinline{cd} does not do something useful on arbitrary binary trees, only the trees built by \lstinline{cvt} and \lstinline{cd} itself.
What are the constraints on these trees, and how does \lstinline{cd} exploit them?
%\Josh{To be explicitly responded at the end of S3}
Richard did give some hint: if we compute the sizes of subtrees along their left spines (see the red numbers in Figure~\ref{fig:map_g_cd}),%
\Jeremy{``Aha!''}
$[1,2,3,4,5]$, $[1,3,6,10]$, and $[1,4,10]$ are the first three diagonals of Pascal's triangle --- the trees are related to binomial coefficients!
So the name \lstinline{B} could refer to `binomial' in addition to `binary'.

Given these clues, how do we prove that \lstinline{cd} indeed does the job --- bringing values about related immediate sublists together?
In fact, how do we even write that down as a formal specification?
And how does that help me to prove that \lstinline{td} equals \lstinline{bu}?
%\Josh{and proving \lstinline{td} equals \lstinline{bu}. Shin: added.}

I fear that there will be plenty of complex proofs waiting ahead for me.

%\todo[inline]{Recap of what Richard's paper wanted to do: transforming a top-down algorithm (which acts as a specification) to a bottom-up algorithm, which `I' (Shin) had already worked out a simplified version; explain why the base cases have to be singleton lists; the role of \lstinline{cd} in the bottom-up algorithm, intuitively; relationship to binomial cofficients}

%But I still couldn’t see, \emph{formally}, how to make sense of the definition of \lstinline{cd} or get from the definition to a correctness proof of \lstinline{bu}.
%\todo{Main question; even suggest there's a lot of proving ahead (actually not)}

\section{Indexed Data Types of Binomial Trees}

To start off with something easier:
One thing in \lstinline{cd} that's been bothering me is the use of \lstinline{zipBWith}.
Why is the zip justified~--- what if the two trees have different shapes?
A reasonable guess is that the two trees \emph{cannot} have different shapes.
Proving that seems to be a good first exercise, because there's a standard solution: capturing the tree shape in its type.
Shape-indexed data types are so common now that I'm tempted to say that they should count as simple types, and they are common even in Haskell.
I prefer a proper dependently typed language though, so I open my favourite editor, and switch to Agda.

The classic example of shape-indexing is, of course, length-indexed lists:
\begin{code}
data Vec : ℕ → Set → Set where
  []   :                Vec    zero    a
  _∷_  : a → Vec n a →  Vec (  suc n)  a
\end{code}
The constructors used in a list of type |Vec n a| are completely determined by the length index~|n|.
The data type definition could even be understood as if it were performing pattern matching on the index:
If the index is |zero|, then the list has to be nil; otherwise the index is a |suc|, and the list has to start with a cons.
(A gang of people~\citep{Chapman-levitation, Ko-pcOrn, Dagand-functional-ornaments} did develop theories for defining data types by pattern matching on indices.)
In the same vein, I write down a shape-indexed version of Richard's \lstinline{B} data type:%
\Jeremy{For consistency here, we should talk earlier about ``level $k$'' rather than ``level $n$''}
\begin{code}
data B : ℕ → ℕ → Set → Set where
  tipZ  :   a                → B n           zero    a
  tipS  :   a                → B (suc  k) (  suc k)  a
  bin   :   B n (suc  k)  a
        →'  B n       k   a  → B (suc  n) (  suc k)  a
\end{code}
The idea is that the \emph{size} of a tree of type |B n k a| with $k \le n$ is precisely the binomial coefficient~|CHOOSE n k|, and there are no trees of type |B n k a| when $k > n$.
Like |Vec|, the indices $n, k$ determine the constructors:%
\footnote{It would seem that both |tipS| and |bin| are possible for the case |B(C sk sk) a| (so that the indices don't determine the constructor), but |bin| is actually impossible because its left sub-tree would have type |B(C sk ssk) a|, which can be shown to be uninhabited.}
If |k|~is |zero|, then the tree is a |tipZ| with one element (|CHOOSE n 0 =' 1|).
Otherwise, if |n|~is |suc k|, then the tree is a |tipS| with also one element (|CHOOSE sk sk =' 1|).
Otherwise the tree is a |bin|, and the sizes |CHOOSE n sk| and |CHOOSE n k| of the two sub-trees add up to the intended size |CHOOSE sn sk| of the whole tree.
The trees are now truly \emph{binomial} rather than just binary, formalising Richard's hint about sizes.
I should probably write |B(C n k)| for |B n k| to relate it to |CHOOSE n k| notationally.

And now I can give a more precise type to \lstinline{cd}:
\begin{code}
cd : (SUPPRESSED(1 ≤ k)) → (SUPPRESSED(k < n)) → B(C n k) a → B(C n sk) (Vec (1 + k) a)
\end{code}
It takes as input the data for level~$k$ out of $n$~levels in the sublist lattice~(\cref{fig:sublists-lattice}), with $1 \le k < n$; these are the results for each of the |CHOOSE n k| $k$-sublists of the original $n$-list.
And it returns as output the components for level~|1 + k|; there are |CHOOSE n (sk)| of these, each a |(1 + k)|-list (to be fed into \lstinline{g}).
%The input data can conveniently be stored in a tree indexed by $n,k$, and the output indexed by $n,1+k$.
As I transcribe \lstinline{cd} interactively with Agda, the tree shapes are automatically kept track of in the indices all the time.
For example, in the |bin t u| case, Agda tells me that |t : B(C sn ssk) a| and |u : B(C sn sk) a|, so |cd u : B(C sn ssk) (Vec (2 + k) a)|, and it's indeed safe to zip |t|~and |cd u| together using the zip function that takes only two trees \emph{of the same shape} and returns another tree of that shape:
\begin{code}
zipBWith : (a → b → c) → B(C n k) a → B(C n k) b → B(C n k) c
\end{code}
%In fact, that type is so informative that only one program inhabits it, and that program can be found automatically by proof search.
%(Well, at least the positive clauses are automatic. Proving absurdity of the other clauses takes a little effort.)
The transcription finishes without any problem, so my guess is correct, and it's conveniently verified just by type checking.
However, the transcription does involve a bit of extra proof burden about the two (greyed out) `side conditions' |1 ≤ k| and |k < n| of |cd|, which I temporarily ignore whenever I call |cd| (as in |cd u|, as if |cd| were a function with only one explicit argument).
Agda ensures that I don't forget about these ignored conditions in the final code though.

So much for the shape.
But how do I know that the contents are correct~--- that \lstinline{cd} is correctly rearranging the values?
\Jeremy{I don't really understand the TODO: ``What to say? Need a spec: the equational one using \lstinline{choose} (marking the element positions with sub-lists and specifying where the elements should go); but requires a lot of proving''. Update 20240124: A lot of equational reasoning. Do we mention Shin's paper? Josh: This has to be in the Afterword.}

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
The induction structure is the same as how |B(C n k)| analyses its indices, except that here I need to deal with a list \lstinline{xs} rather than just its length.
This \lstinline{choose} generalises Richard's \lstinline{dc} (which computes the immediate sublists):
\lstinline{dc xs} can be redefined as \lstinline{flatten (choose (length xs - 1) xs)}, where
\begin{lstlisting}
flatten :: B a -> L a
flatten (Tip x)    =  [x]
flatten (Bin t u)  =  flatten t ++ flatten u
\end{lstlisting}
Then Richard could have specified \lstinline{cd} by
\[ \text{\lstinline{cd (choose k xs)}} \equals \text{\lstinline{mapB (flatten . choose k) (choose (k+1) xs)}}
\hfill (\ast)
\]
Informally:
Given all the \lstinline{k}-sublists of an \lstinline{n}-list \lstinline{xs}, \lstinline{cd} should rearrange and duplicate them into the appropriate positions for the \lstinline{(k+1)}-sublists, where in the position for a particular \lstinline{(k+1)}-sublist, the result should be the list of all its immediate sublists as computed by \lstinline{flatten . choose k}.

I could go on and derive the definition of \lstinline{cd} from the specification, finishing what Richard could've done in his paper, and maybe switching to |B(C n k)| throughout to make the shapes clear.
But I can already imagine that would involve a large amount of tedious equational reasoning, and I'm not thrilled.

My editor is still running Agda and showing the shape-indexed version of |cd|, with |B(C n k)| in its type.
The whole point of programming with inductive families such as |B(C n k)| is to `say more and prove less':
Encode more properties in the indices, so that those properties are automatically taken care of as programs construct and deconstruct indexed data, requiring less proofs.
Instead of just the shapes, maybe it's possible to extend |B(C n k)| and encode the \emph{entire} specification of \lstinline{cd} in its type?

What the specification says is basically that \lstinline{cd} should transform a tree produced by \lstinline{choose} into another one also produced by \lstinline{choose} and then processed using a \lstinline{mapB}.
I suppose I could force a tree to be the result of \lstinline{mapB h (choose k xs)} for some~\lstinline{h} (which is the common form of the input and output trees of \lstinline{cd}) by adding \lstinline{h} and \lstinline{xs} as indices to |B(C n k)|:
\begin{code}
  data B' : (n k : ℕ) (b : Set) → (Vec k a → b) → Vec n a → Set where
    tipZ  :   (y : b) (e : y ≡ h []  )             → B' n           zero    b h xs
    tipS  :   (y : b) (e : y ≡ h xs  )             → B' (suc  k) (  suc k)  b h xs
    bin   :   B' n (suc  k)  b    h            xs
          →'  B' n       k   b (  h ∘ (x ∷_))  xs  → B' (suc  n) (  suc k)  b h (x ∷ xs)
\end{code}
This is a somewhat complex extension to |B(C n k)|, but the programming methodology is still the same:
Perform `pattern matching' on the indices, and specify what should be in the tree in each case.
The pattern-matching structure follows the definition of \lstinline{choose}.
In the first case, \lstinline{choose} returns~\lstinline{Tip []}, so the tree should be a |tipZ| whose element~|y| should be accompanied with a proof~|e| that |y|~equals |h []|, so that |tipZ y e| `is' \lstinline{mapB h (Tip [])}.
The second case is similar.
In the third case, the first thing I do is switch from Richard's snoc pattern \lstinline{xs ++ [x]} to a cons index |x ∷ xs| --- this just `reverses' the list and shouldn't break anything, as long as the snoc in \lstinline{mapB (++[x])} is also switched to a cons consistently.
The first inductive call of \lstinline{choose} easily translates into the type of the left sub-tree.
The right sub-tree should be the result of \lstinline{map h (map (x:) (choose k xs))}, where (luckily) the two maps can be fused into a single \lstinline{map (h . (x:))}, so the type of the second sub-tree uses the index |h ∘ (x ∷_)| instead of~|h|.

I feel an urge to see with my own eyes that the |B'|~data type works as intended, so I write a tree with `holes' (missing parts of a program) at the element positions, and let Agda tell me what types the holes should have:
\begin{code}
testB' : {h : Vec 2 Char → b} → (B'_ 4 2) b h "abcd"
testB' = bin  (bin  (tipS  (GOAL(b)(G0)) (GOAL(?0 ≡ h "cd")(G1)))
                    (bin  (tipS  (GOAL(b)(G2))  (GOAL(?2 ≡ h "bd")(G3))  )
                          (tipZ  (GOAL(b)(G4))  (GOAL(?4 ≡ h "bc")(G5))  )))
              (bin  (bin  (tipS  (GOAL(b)(G6))  (GOAL(?6 ≡ h "ad")(G7))  )
                          (tipZ  (GOAL(b)(G8))  (GOAL(?8 ≡ h "ac")(G9))  ))
                    (tipZ  (GOAL(b)(G10)) (GOAL(?10 ≡ h "ab")(G11))))
\end{code}
As expected, all the constructors are determined by the indices.
The goal types of the even-numbered holes are all~|b|, and the odd-numbered holes require proofs that the even-numbered holes are equal to |h zs| for all the |2|-sublists |zs| of |"abcd"|.
It does work!

|B'|~doesn't look bad, but I can't help raising my eyebrow.
With some more effort, I suppose I could refine the type of |cd| to use~|B'| and encode the full specification, but the refined |cd| would need to manipulate the equality proofs in those trees, and maybe eventually I'd still be doing essentially the same tedious equational reasoning that I want to avoid.
Another problem is that the upgraded |cd| would only work on trees of sublists, whereas the original \lstinline{cd} works on trees of \emph{any} type of values.
Indeed, the specification talks about the behaviour of \lstinline{cd} on trees of sublists only; by encoding the specification in the type, I'd actually restrict |cd| to trees of sublists.
That doesn't sound too useful.

Still, I can't take my eyes off the definition of~|B'|.
The way it absorbs the definition of \lstinline{choose} looks right.
If only the elements aren't restricted to pairs of the form |y : b| and |e : y ≡ h zs|\ldots

A lightbulb lights up over my head.
\begin{code}
data BT : (n k : ℕ) → (Vec k a → Set) → Vec n a → Set where
  tipZ  :   p []                             → BT n           zero    p xs
  tipS  :   p xs                             → BT (suc  k) (  suc k)  p xs
  bin   :   BT n (suc  k)   p            xs
        →'  BT n       k (  p ∘ (x ∷_))  xs  → BT (suc  n) (  suc k)  p (x ∷ xs)
\end{code}
Just generalise the element type!
More specifically, generalise that to a \emph{type family} |p : Vec k a → Set| indexed by |k|-sublists.
Then both |B(C n k) a|~and~|B'_ n k b h xs| become special cases by specialising~|p| to |const a| (and supplying any |n|-list as the last index) and to |λ zs → Σ[ y ∈ b ] y ≡ h zs| respectively!

I wasn't expecting this generalisation.
After taking a moment to calm down, I look more closely at this new, unifying data type.
The index~|p| in |BT| replaces~|h| in~|B'|, and is similarly applied to all the sublists of a particular length.
What's different is that |p|~is applied to a sublist to get the whole element type in a tip.
So, in general, all the elements in a tree of type |BT_ n k p xs| have \emph{distinct} types, which are |p ys| for all the |k|-sublists |ys| of the |n|-list |xs|.
To see a sample:
\begin{code}
testBT : {p : Vec 2 Char → Set} → (BT_ 4 2) p "abcd"
testBT = bin  (bin  (tipS  (GOAL(p "cd")(G0))  )
                    (bin  (tipS  (GOAL(p "bd")(G1))  )
                          (tipZ  (GOAL(p "bc")(G2))  )))
              (bin  (bin  (tipS  (GOAL(p "ad")(G3))  )
                          (tipZ  (GOAL(p "ac")(G4))  ))
                    (tipZ  (GOAL(p "ab")(G5))  ))
\end{code}
It's simpler to think of a tree of type |BT_ n k p xs| as a table with all the |k|-sublists of~|xs| as the keys, and for each key~|ys| there's an entry of type |p ys|.
(So the `T' in |BT| stands for both `tree' and `table'.)%
\todo{how to find an entry}

This |BT| definition is really intriguing\ldots
The ad hoc feeling I had with~|B'| is completely gone.
This is probably because there's no arbitrary information in |BT| with respect to \lstinline{choose}.
Most likely, there is a way to derive |BT| from \lstinline{choose}, and that'll work for a whole class of functions.
I mean, the type of |BT_ n k : (p : Vec k a → Set) → Vec n a → Set| is a continuation-passing version of some |Vec n a ↝ Vec k a|, which would be the (shape-indexed) type of a version of \lstinline{choose} that non-deterministically returns a sublist.
And the index~|p| works like a continuation too.
Take the (expanded) type of |bin| for example:
\begin{code}
bin  :   BT n (suc  k)  (λ ys  → p ys)        xs
     →'  BT n       k   (λ zs  → p (x ∷ zs))  xs  → BT (suc n) (suc k) p (x ∷ xs)
\end{code}
I can read it as `to compute a |(1 + k)|-sublist of |x ∷ xs| and return it with continuation~|p|, either compute a |(1 + k)|-sublist |ys| of |xs| and return |ys| directly, or compute a |k|-sublist |zs| of |xs| and return |x ∷ zs|'.
All the `returned results' are then collected in a tree as the indices of the element types.
Another similar and familiar example is
\begin{code}
data All : (a → Set) → Vec n a → Set where
  []   :                   All p []
  _∷_  : p x → All p xs →  All p (x ∷ xs)
\end{code}
which should be derivable from the function that non-deterministically returns an element of a list.
I'm onto something general --- maybe it's interesting enough for an ICFP paper!%
\todo{Optional paragraph about generality}

That paper will have to wait though --- I've still got a problem to solve:
How do I use |BT| to specify \lstinline{cd}?

What's special about |BT| is that the element types are indexed by sublists, so I know from the type of an element with which sublist it associates.
That is, I can now directly say `values associated with sublists' and how they should be rearranged, rather than indirectly specify the rearrangement in terms of sublists and then extend to other types of values through parametricity.
%\Shin{Can we give some explanation why this type enforces $(\ast)$?
%The way I understand it is that the input is a table containing all length |k| %sublists and they all satisfy |p|, thus matching \lstinline{choose n k};
%the output chooses |sk| elements and, for each of them, chooses all length |k| %sublists, and they all satisfy |p|, thus kind of matching the two %\lstinline{choose}s. What is the significance of |p| here? And we might want to %mention that \lstinline{flatten} is gone.
%SCM: it's much clearer now. Removing this comment.}
|BT_ n k p xs| is the type of a table of |p|-typed values associated with the |k|-sublists of |xs|, and that's precisely the intended meaning of \lstinline{cd}'s input.
What about the output?
It should tabulate the |(1 + k)|-sublists of |xs|, so the type should be |BT_ n sk q xs| for some |q : Vec (1 + k) a → Set|; for each sublist |ys : Vec (1 + k) a|, I want a list of |p|-typed values associated with the immediate sublists of |ys|, which are |k|-sublists, and that's precisely a tree of type |BT_ sk k p ys| --- the shape of that tree is even a list!\todo{flatten}
Therefore the whole type is
\begin{code}
retabulate : (SUPPRESSED(k < n)) → (BT_ n k) p xs → (BT_ n sk) ((BT_ sk k) p) xs
\end{code}
which is parametric in~|p| (so, like \lstinline{cd}, the elements can have any types).
I think it's time to rename \lstinline{cd} to something more meaningful, and decide to use `|retabulate|' because I'm moving values in a table into appropriate positions in a new (nested) table with a new tabulation scheme.%
\Jeremy{I'd like to think of a better name.}
And a side condition |k < n| is needed to guarantee that the output shape |BT_ n sk| is possible.

I go on to transcribe \lstinline{cd} into |retabulate|,
\begin{code}
retabulate : (SUPPRESSED(k < n)) → BT(C n k) p xs → BT(C n sk) (BT(C sk k) p) xs
retabulate {xs =' _ ∷ []     }  (tipZ y)  =  tipS  (tipZ y)
retabulate {xs =' _ ∷ _ ∷ _  }  (tipZ y)  =  bin   (retabulate (tipZ y)) (tipZ (tipZ y))
retabulate (bin t         (tipZ y)  )     =  bin   (retabulate t) (mapBT (_∷ᴮᵀ (tipZ y)) t)
retabulate (bin (tipS y)  u         )     =  tipS  (y ∷ᴮᵀ u)
retabulate (bin t         u         )     =  bin   (retabulate t)
                                                   (zipBTWith _∷ᴮᵀ_ t (retabulate u))
\end{code}
where the map function is the expected one,
\begin{code}
mapBT : (∀ {ys} → p ys → q ys) → ∀ {xs} → (BT_ n k) p xs → (BT_ n k) q xs
mapBT f (tipZ  p)  = tipZ  (f p)
mapBT f (tipS  p)  = tipS  (f p)
mapBT f (bin t u)  = bin   (mapBT f t) (mapBT f u)
\end{code}
and a cons function can be introduced for |BT_ sk k|-trees/lists:
\begin{code}
_∷ᴮᵀ_ : p xs → BT(C sk k) (p ∘ (x ∷_)) xs → BT(C ssk sk) p (x ∷ xs)
y ∷ᴮᵀ t = bin (tipS y) t
\end{code}
(The type of |_∷ᴮᵀ_| is slightly complex, but Agda pretty much infers it for me.)
Everything related to the side condition |k < n| is omitted to make it easier to compare with \lstinline{cd}; also omitted are the two cases |tipS _| and |bin _ (tipS _)|, whose shapes are proved to be impossible.
I forgot about another side condition |1 ≤ k|, but that leads to two additional |tipZ| cases (which are fairly easy to figure out from the type information) instead of preventing me from completing the definition.

\todo[inline]{Compare \lstinline{cd} and |retabulate|.
(In particular, the additional |tipZ| cases of |retabulate| are responsible for producing a level-1 table (with as many elements as |xs|) from a level-0 table, which is a |tipZ|.
Since |xs|~is available as an index, there's now enough information for going from level~0 to level~1 (on the sublist lattice).)
The definition has been verified simply by finding the (or rather, a) right type for it!
There's actually no need to understand the definition of \lstinline{cd}/|retabulate| now, but I can still go through a case or two to see how well type-directed programming works.}

As I filled in the holes, I didn't feel I had much of a choice --- in a good way, because that reflected the precision of the type.
In fact, looking at the type more closely, I suspect that the extensional behaviour of |retabulate| is completely determined by the type (so the type works as a nice and tight specification):
The shape of the output table is completely determined by the indices; moreover, all the input elements have distinct types in general, so each element in the output table has to be the only input element with the required type --- there is no choice to make.
Formally, the proof will most likely be based on parametricity.
That'll probably be a fun exercise\ldots but I'll leave that for another day.%
\Jeremy{Should this move to the Afterword?}

\section{Dependently Typed Algorithms}

Right now I'm more eager to find out why the bottom-up algorithm \lstinline{bu} equals the top-down \lstinline{td}.
Will dependent types continue to be helpful?
I should try and find out by transcribing the two algorithms into Agda too.

I go back to the type of the combining function~\lstinline{g}.
This type \lstinline{L b -> b} has been making me blink involuntarily whenever I see it, because it says so little that \lstinline{g}~can have arbitrarily wild behaviour, which is unsettling.
The intention that \lstinline{g}~should combine solutions for all the immediate sublists of a list into a solution for the list is nowhere to be seen.

But now I have the right vocabulary to say the intention precisely in Agda:
I can use |BT| to say things about all sublists of a particular length, and to say `a solution for a list' (instead of just `a solution') I should switch from a type~\lstinline{b} to a type family
\begin{code}
s : {k : ℕ} → Vec k a → Set
\end{code}
such that |s ys| is the type of solutions for |ys|.
So
\begin{temp}
\begin{code}
g : BT(C ssk sk) s ys → s ys
\end{code}
\end{temp}
I look at this with an involuntary smile --- now that's a nice and informative type!
It says concisely and precisely what |g|~does: compute a solution for any |ys : Vec (2 + k) a| from a table of solutions for all the length-|(1 + k)| (that is, immediate) sublists of |ys|.

The smile quickly turns into a frown though.
I still don't feel comfortable with |BT(C ssk sk)|, where the indices are apparently not the most general ones --- why not |BT(C sk k)|?

I wrote |BT(C ssk sk)| because that was what Richard wanted to say:
Richard used singleton lists as the base cases instead of the empty list, so \lstinline{g}~was applied to solutions for sublists of length at least~|1|, hence the subscript |1 + k|.
But the most general type
\begin{code}
g : BT(C sk k) s ys → s ys
\end{code}
looks just fine.
In particular, when |k|~is~|0|, the type says that |g|~should compute a solution for a singleton list from a solution for the empty list (the only immediate sublist of a singleton list), which seems reasonable\ldots

\ldots And indeed it is reasonable!
(A red background is applied to the previous type of~|g| to indicate that there's a newer version.)

When I discovered the extra |tipZ| cases of |retabulate|, I saw that the bottom of the sublist lattice~(\cref{fig:sublists-lattice}) may be retained after all.
That observation is confirmed here.
Instead of starting with solutions for singleton lists, I can start with a given solution for the empty list
\begin{temp}
\begin{code}
e : s []
\end{code}
\end{temp}
at level~0 of the completed lattice and work upwards using~|g|.
In particular, there's no problem going from level~0 to level~1, because there's now additional information in the indices so that |g|~knows for which singleton list a solution should be computed.
Making types precise has also helped to find a more general formulation of the immediate-sublist computation!

And it's not just any computation --- it's now an alternative \emph{induction principle} for lists where the inductive case assumes that the induction hypothesis holds for all the immediate sublists.
(I guess I've been instinctively drawn towards induction principles like most if not all dependently typed programmers.)
\begin{temp}
\begin{code}
ImmediateSublistInduction : Set₁
ImmediateSublistInduction =
  {a : Set}  (  s   : {k : ℕ} → Vec k a → Set)
             (  e   : s [])
             (  g   : {k : ℕ} {ys : Vec (1 + k) a} → BT(C sk k) s ys → s ys)
  {n : ℕ}    (  xs  : Vec n a) → s xs
\end{code}
\end{temp}
The type looks very nice, but I'm still worried:
Will it be possible to transcribe \lstinline{td} and \lstinline{bu} for this type nicely, that is, without ugly stuff like type conversions (|subst|, |rewrite|, etc)?

The only way to find out is to try and write some programs.
(Sadly, I don't think there's any theory that helps me see more quickly whether a type admits nice programs or not.)
I start transcribing \lstinline{td}.
The only component of which I still don't have a dependently typed version is \lstinline{dc}, which I've generalised to \lstinline{choose}.
Transcribing \lstinline{choose} is mostly a standard exercise in dependently typed programming:
\begin{code}
choose : (n k : ℕ) → k ≤↑ n → (xs : Vec n a) → BT(C n k) Exactly xs
choose _           zero    _          _         = tipZ  (exactly []  )
choose (suc k)  (  suc k)     zero    xs        = tipS  (exactly xs  )
choose (suc n)  (  suc k)  (  suc d)  (x ∷ xs)  =
  bin (choose n (suc k) d xs) (mapBT (mapExactly (x ∷_)) (choose n k (incr d) xs))
\end{code}
The key ingredient is the |BT(C n k)| in the result type, which tabulates all the length-|k| sublists as the indices of the element types.
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
Different from the Haskell version, I need to make the Agda function total by saying explicitly that the length~|n| of the list |xs| is at least~|k|, so that there are enough elements to choose from.
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

I step back and take another look at |choose|.
One thing starts to bother me:
|Exactly x| is a type that has a unique inhabitant, so I could've used the unit type~|⊤| as the element type instead, and I'd still give the same amount of information, which is none!
That doesn't make a lot of sense --- I thought I was computing all the length-|k| sublists and returning them in a table, but somehow those sublists didn't really matter, and I could just return a blank table of type |BT(C n k) (const ⊤) xs|\ldots?

Hold on, it's actually making sense\ldots

It's because all the information is already in the table structure of |BT|.
Indeed, I can write
\begin{code}
mapBT (λ { {ys} tt → exactly ys }): BT(C n k) (const ⊤) xs → BT(C n k) Exactly xs
\end{code}
to recover a table of |Exactly|'s from just a blank table by replacing every |tt| (the unique inhabitant of~|⊤|) with the index |ys| there.
What |choose| does is not really compute the sublists, which have already been `computed' by the definition of |BT|.
Instead, |choose| merely affirms that there is a table indexed by all the length-|k| sublists of a length-|n| list whenever |k ≤↑ n|; the elements in the table don't matter, and can well be~|⊤|.

So, instead of |choose|, I can use%
\Shin{I find |blank| clearer if we include |xs| as an simplcit argument\ldots\ Josh: Added.}
\begin{temp}
\begin{code}
blank : (n k : ℕ) → k ≤↑ n → {xs : Vec n a} → BT(C n k) (const ⊤) xs
blank _          zero    _          = tipZ tt
blank (suc k) (  suc k)     zero    = tipS tt
blank (suc n) (  suc k)  (  suc d)  = bin (blank n (suc k) d) (blank n k (incr d))
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

I look at the monster I created, aghast.
Sure, the definition type-checks, but oh my\ldots it's terribly ugly, and for so many reasons:
\begin{inlineenum}
\item The induction is on~|n|, which shouldn't have been an implicit argument;
\item in the base case, I have to match |xs| with~|[]| to make it type-correct to return~|e|, but that could've been avoided if I set |e : {xs : Vec 0 a} → s xs|;
\item in the inductive case, |xs| doesn't need to be explicit because it's passed around only implicitly in the indices on the right-hand side;
\item I can get rid of the~|λ| around the inductive call to |td| if I make |ys| implicit and add a dummy |⊤|~argument.
\end{inlineenum}
In fact, if I add a dummy |⊤|~argument to |e|~and |blank| as well, I can make the definition point-free like in Richard's paper --- a temptation I cannot resist!
So I revise the induction principle,
\begin{code}
ImmediateSublistInduction : Set₁
ImmediateSublistInduction =
  {a : Set}  (  s  : {k : ℕ} → Vec k a → Set)
             (  e  : {ys : Vec 0 a} → ⊤ → s ys)
             (  g  : {k : ℕ} {ys : Vec (1 + k) a} → BT(C sk k) s ys → s ys)
             (  n  : ℕ) {xs : Vec n a} → ⊤ → s xs
\end{code}
add the dummy |⊤|~argument to |blank| (while suppressing the inequality argument from now on),
\begin{code}
blank : (n k : ℕ) → (SUPPRESSED(k ≤↑ n)) → {xs : Vec n a} → ⊤ → BT(C n k) (const ⊤) xs
\end{code}
and get my beautiful point-free |td|:
\begin{code}
td : ImmediateSublistInduction
td s e g    zero    = e
td s e g (  suc n)  = g ∘ mapBT (td s e g n) ∘ blank(C sn n)
\end{code}
The revised |ImmediateSublistInduction| may not be too user-friendly, but that can be amended later (when there's actually a user).

And it'll be wonderful if the revised |ImmediateSublistInduction| works for |bu| too!
I go on and transcribe \lstinline{bu}:
\begin{code}
bu : ImmediateSublistInduction
bu s e g n = unTip ∘ loop 0 (GOAL(0 ↓≤ n)(G0)) ∘ mapBT e ∘ blank(C n 0)
  where
    loop : (k : ℕ) → k ↓≤ n → BT(C n k) s xs → BT(C n n) s xs
    loop n    zero    = id
    loop k (  suc d)  = loop (1 + k) d ∘ mapBT g ∘ retabulate
\end{code}
The initialisation is done (point-free!) by creating a blank level-|0| table and using |mapBT e| to fill in the initial solution for the empty list.
Then the |loop| function increases the level to~|n| by repeatedly retabulating a level-|k| table as a level-|(1 + k)| table and filling in solutions for all the length-|(1 + k)| sublists using~|g|.
Finally, a solution for the whole input list is extracted from the level-|n| table using
\begin{code}
unTip : BT(C n n) p xs → p xs
unTip             (tipS  p) = p
unTip {xs =' []}  (tipZ  p) = p
\end{code}
(The |bin| case actually needs to be listed and proved impossible.)
The argument/counter~|k| of |loop| should satisfy the invariant |k ↓≤ n|; the data type |m ↓≤ n| is another version of natural number inequality, which is dual to |_≤↑_| in the sense that |n|~is fixed throughout the new definition, and |m|~moves away from~|n|:
\begin{code}
data _↓≤_ : ℕ → ℕ → Set where
  zero  :               n  ↓≤' n
  suc   : suc m ↓≤ n →  m  ↓≤' n
\end{code}
The |loop| function performs induction on the distance |k ↓≤ n|; the counter~|k| goes up as the distance decreases in inductive calls, and eventually reaches~|n| when the distance becomes |zero|.
The remaining goal |0 ↓≤ n| in |bu| is actually non-trivial, but the Agda standard library covers that.

Another beautiful (by which I mean point-free) implementation of |ImmediateSublistInduction|!%
\Josh{The obsession with the point-free style actually helps to transit to the categorical development (but I want to tone it down a bit).}

Okay, I've made the type of both |td| and |bu| precise.
How does this help me prove |td| equals |bu|?
The definitions still look rather different except for their type.

And the type is an induction principle.

Is it possible to have extensionally different implementations of an induction principle?

Think about the induction principle of natural numbers.
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
The same argument works for |ImmediateSublistInduction| --- any function of the type satisfying unary parametricity is pointwise equal to a variant of |td|.
I finish the Agda proofs for both induction principles in a dreamlike state.

Yeah, I have a proof that |td| equals |bu|.

Well, strictly speaking I don't have one yet.
(Vanilla) Agda doesn't have internal parametricity, so I'd need to prove the parametricity of both |td| and |bu|, painfully.
But there shouldn't be any surprise.

Somehow I feel empty though.
I was expecting a more traditional proof based on equational reasoning, which may require more work, but allows me to compare what |td| and |bu| do \emph{intensionally}, which is an aspect overlooked from the parametricity perspective.
Despite having a proof now, I think I'm going to delve into the definitions anyway to get a clearer picture of their relationship.

\section{Categories of Families of Types and Functions}

\todo[inline]{Not a category theory tutorial; more like a companion to a tutorial or a textbook, or an invitation to learn categorical tools (as well as dependent types and string diagrams for that matter) by providing intuitions and practical examples from the immediate-sublist computation; mention this meta-level goal in the abstract and the afterword.}

Another important hint Richard left was \emph{naturality}, a category-theoretic notion which he used a lot in his proofs.
In functional programming, naturality usually stems from parametric polymorphism:
All parametric functions, such as \lstinline{cd} and \lstinline{unTip}, satisfy naturality.
I've got some parametric functions too, such as |retabulate| and |unTip|, but their dependent function types with all the (somewhat annoying) indices are making me disoriented.
I need to reorient myself by figuring out which \emph{category} I'm in now.%
\Josh{Can we make it clearer what `disoriented' and `reorient' means?}

Functional programmers are familiar with types and functions, and know when functions can be composed sequentially --- when adjacent functions meet at the same type.
And it's possible to compose an empty sequence of functions, in which case the result is an identify function.
Categories are settings in which the same intuition about sequential composition works:
Instead of types and functions, the categorical programmer can switch to work with some \emph{objects} and \emph{morphisms} specified by a category, where each morphism is labelled with a source object and a target object (like the source and target types of a function), and morphisms can be composed sequentially when adjacent morphisms meet at the same object.
And, like identity functions, there are identity morphisms too.
Working in a new setting that's identified as a category (or some crazier variant that supports more operations in addition to sequential composition) is a blessing for the functional programmer: It means that the programmer can still rely on some of their intuitions about types and functions to navigate in the new setting.
(And the formal definitions of various kinds of category make precise which intuitions remain reliable.)
More importantly, some notions that prove to be useful in functional programming can be defined generically on categories and systematically transported to other settings.

A clue about the kind of category I'm in is that I'm tempted to say `|retabulate| transforms a tree of |p|'s to a tree of trees of |p|'s':
When a simply typed functional programmer says `a tree of something', that `something' is a type, that is, an object in the category |Fun| of types and functions, but here |p|~is a type family.
So I've left |Fun| and landed in a kind of category where the objects are type families.

There are quite a few versions of `categories of families' with different functionalities.
I go through the types of the components (such as |retabulate|) used in the algorithms to determine what I need, and it seems that the simplest version suffices:
%\Jeremy{or ``is the simplest one''?}
Given an index type |a : Set|, a category of families |Fam' a| has objects of type
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
I can fit |blank(C n k)| into |Fam' (Vec a n)| by lifting its |⊤|~argument to a type family |const ⊤| (that is, an object of the category):
\begin{code}
blank(C n k) : const ⊤ ⇉ BT(C n k) (const ⊤)
\end{code}
The base and inductive cases of |ImmediateSublistInduction| fit into these |Fam'| categories too:
Given |a : Set| and |s : ∀ {k} → Fam (Vec k a)|, I can write
\begin{code}
g  : BT(C sk k) s  ⇉' s
e  : const ⊤       ⇉' s
\end{code}
It's important to add that |e|~is a morphism in |Fam' (Vec 0 a)|, so that |e|~gives a solution for (only) the empty list.
%Alternatively, writing |e : const ⊤ ⇉ s {0}| also makes it clear that the morphism is in |Fam' (Vec 0 a)| (because |s {0} : Fam (Vec 0 a)| is an object in |Fam' (Vec 0 a)|), but that looks slightly more verbose.

All I've done is merely a bit of abstraction that hides part of the indices, which might even be described as cosmetic.
However, by rephrasing the types in the categorical language, now I can start talking about \emph{functors} and \emph{natural transformations} sensibly.

Normally a data type |D a| that's parametric in~|a| can be thought of as the type of containers that are made up of the constructors of~|D| and hold elements of type~|a|.
Categorically, |D|~is the object part of a \emph{functor}, which maps an object~|a| in one category to an object |D a| in a possibly different category.
The two layers of data, that is, constructors and elements, are independent in the sense that each layer can be arbitrarily transformed without affecting the other layer.

The independent transformation of the inner layer is described by the morphism part of a functor.
Functional programmers are familiar with the function |map(sub D) : (a → b) → (D a → D b)| that (normally) comes with~|D| and applies a function to all the elements (the inner layer) without changing the constructors of~|D| (the outer layer).
Categorically, `arbitrary transformation' means anything that can happen within a category, namely morphisms and their sequential composition.
So any morphism~|f| from~|a| to~|b| should give rise to a morphism |map(sub D) f| from |D a| to |D b| that's essentially still just~|f| because it does nothing to the outer |D|-layer; in particular, if the morphism is a composition |f · f'|, then |map(sub D) (f · f')| should still be a composition |map(sub D) f · map(sub D) f'| (and, in the special case of composing an empty sequence of morphisms, |map(sub D) id = id|).
A functor consists of an object part (such as~|D|) and a morphism part (|map(sub D)|), with properties that establish the independence of the functor layer from whatever happens in the inner layer.

On the other hand, the independent transformation of the outer layer is performed by \emph{natural transformations}.%
\todo{\ldots}

\todo[inline]{Make all these less abstract by mixing in concrete stuff such as |BT|?}

%\todo[inline]{One source of complexity is the indices, which are getting annoying and need a bit of management.
%In a sense, |retabulate| is still a familiar functional program that transforms a tree of~|p|'s to a tree of trees of~|p|'s, parametrically in~|p|.
%Category theory helps us see that and make it precise.
%Functional programmers are familiar with types and functions; abstract them as objects and morphisms so that we can specialise them to something new (in this case families of types and functions, or (proof-relevant) predicates and pointwise implications) and work with the new stuff using the same notation and intuition.
%In particular, |BT(C n k)| is a real functor, just in the new categories, and |mapBT| is the functorial map.}

\section{String-Diagrammatic Algorithms}

%Now I see that I'm pretty much still writing ordinary functional programs, so there's a better chance that I can transfer what Richard did with his programs to my setting.
%Now I know in which categories I should talk about them.

I have an additional tool that Richard didn't: \emph{string diagrams}.
I've seen how dramatically string diagrams simplify proofs about natural transformations (and indeed other stuff, for which the simplification can be even more dramatic), so it's probably worthwhile to take a look at the two algorithms from a string-diagrammatic perspective.

So I had better refresh my memory of string diagrams\ldots

%\todo[inline]{Richard already pointed out that naturality is the key; try string diagrams!}

\todo[inline]{Revise these to highlight the diagrammatic intuition about layer independence, which is already discussed in the previous section.}

At a higher abstraction level, what a natural transformation does is transform one functor into another.
For example, |retabulate| transforms the functor |BT(C n k)| into the composition of functors |BT(C n sk) ∘ BT(C sk k)|, while |unTip| transforms the functor |BT(C n n)| into the identity functor.%
\Josh{Cover these in the previous section; this section focuses on string diagrams.}
String diagrams present such `type information' as two-dimensional pictures:
Natural transformations are represented as dots, with input wires attached below and output wires above, where the wires represent functors.
(I learned string diagrams mainly from \citet{Coecke-PQP}, so my string diagrams have inputs below and outputs on top.)%
\Josh{Maybe draw these `live' rather than present them as facts.}
\[ \tikzfig{pics/retabulate-unTip} \]
Functor composition is represented as juxtaposition of wires, and the identity functor is omitted (being the unit of functor composition). So |retabulate| has two output wires, and |unTip| has none.

Any two natural transformations |α : ∀ {a} → F a → G a| and |β : ∀ {a} → G a → H a| can be composed \emph{sequentially} into |β ∘ α : ∀ {a} → F a → H a|, which is drawn in a string diagram as |α|~and~|β| connected by the middle wire with label~|G| (obscuring a section of the wire);
|α|~can also be composed \emph{in parallel} with |α' : ∀ {b} → F' b → G' b| into |α ⊗ α' : ∀ {b} → F (F' b) → G (G' b)|, which is drawn in a string diagram as, well, |α|~and~|α'| in parallel.
\[ \tikzfig{pics/vertical} \hspace{.15\textwidth} \tikzfig{pics/horizontal} \]
The two kinds of composition embody the two-dimensional structure of natural transformations.
Natural transformations are laid out vertically in the order they are applied.
Independent of that order/direction/dimension, the functors being transformed also have a composite structure, which is intuitively layers of functors that can be transformed independently of other layers --- that is, in parallel.
These layers are laid out horizontally.

To see why the two-dimensional layout is helpful, consider two ways of defining |α ⊗ α'|: either |map(sub G) α' ∘ α|, where the outer functor~|F| is transformed to~|G| first, or |α ∘ map(sub F) α'|, where the inner functor~|F'| is transformed to~|G'| first.
The two definitions are equal (due to the naturality of~|α|), but the equality can be seen more directly with string diagrams:
\[ \tikzfig{pics/horizontal-definitions} \]
The |map| means skipping over the outer/left functor and transforming the inner functor; so in the diagrams, |α'|~is applied to the inner/right wire.
(The dashed lines are added to emphasise that both diagrams are constructed as the sequential composition of two transformations.)
By placing layers of functors in a separate dimension, it's much easier to see which layers are being transformed, and determine whether two sequentially composed transformations are in fact applied in parallel, so that their order of application can be swapped.
This is abstracted as a diagrammatic reasoning principle:
Dots can be moved upwards or downwards, possibly changing their vertical positions relative to other dots (while stretching or shrinking the wires, which can be thought of as elastic strings), and the meaning of a diagram will remain extensionally the same.

There are many functions that are not natural transformations, but they can be lifted to natural transformations to fit into string diagrams:
A function |f : a → b| can be lifted to have the type |∀ {c} → (const a) c → (const b) c| (where |c|~can range over any non-empty domain) and become a natural transformation from |const a| to |const b|.
I prefer to leave the lifting implicit and just write |a|~and~|b| for wire labels, since it's usually clear that |a|~and~|b| are not functors and need to be lifted.
For some concrete examples, here as string diagrams are the types of the other functions |g|, |e|, |blanks(C n k)| used in the two algorithms:
\[ \tikzfig{pics/g-e-blanks} \]
(Here |⊤|~abbreviates the type family |const ⊤|, which is only an object in the categories of families, and needs to be lifted to |const (const ⊤)| to be a functor for those categories.)%
\todo{Faces are categories?}
With this lifting, the usual naturality can also be reformulated diagrammatically:
For any |f : a → b|,
\[ |map(sub G) f ∘ α = α ∘ map(sub F) f| \hspace{.15\textwidth} \tikzfig{pics/naturality} \]
The reformulation makes it intuitively clear that the naturality of~|α| is about |α|~transforming only the outer functor, independently of whatever is happening inside.

%\todo[inline]{Recap of string diagrams for 2-categories, i.e., layered type structure (composition of functors); layers may be transformed independently of others, and this intuition is captured by the definition of natural transformations.
%The two sides of a traditional naturality equation look rather different, whereas in a diagrammatic equation the two sides are `the same picture', allowing us to change perspectives effortlessly.}

That's enough abstract nonsense --- time to get back to the two algorithms.
I'm not confident enough to work with the recursive definitions straight away, so I take the special case |td s e g 3| of the top-down computation and unfold it into a deeply nested expression.
Translating that into a string diagram is basically writing down all the intermediate type information and laying out the nested type structures horizontally (whereas function composition is laid out vertically).
\Jeremy{``Recall that |s| here is a type family, an object in this category, so is drawn as a wire label, whereas |e| and |g| are natural transformations, so drawn as dots.'' Worth saying?}

\noindent
\begin{minipage}{.55\textwidth}
\begin{code}
td s e g 3 =  g ∘
              mapBT  (  g ∘
                        mapBT  (  g ∘
                                  mapBT e ∘
                                  blanks(C 1 0)) ∘
                        blanks(C 2 1)) ∘
              blanks(C 3 2)
\end{code}
\end{minipage}%
\begin{minipage}{.45\textwidth}
\[ \tikzfig{pics/td} \]
\end{minipage}

All the |mapBT|s are gone in the diagram, because I can directly apply a transformation to the intended layers/wires, rather than count awkwardly how many outer layers I have to skip using |mapBT|, one layer at a time.
Functoriality (|mapBT (f' ∘ f) = mapBT f' ∘ mapBT f|) is also transparent in the diagram, so it's slightly easier to see that |td| has two phases (between which I draw a dashed line):
The first phase constructs deeply nested blank tables, and the second phase fills and demolishes the tables inside out.

It doesn't seem that the string diagram helps much though.
Functoriality is already somewhat transparent in the traditional expression (thanks to the infix notation of function composition), so I don't really need the string diagram to see that |td| has two phases.
Moreover, there's nothing I can meaningfully move in the diagram --- all the transformations here are lifted after all.

Hm. Maybe I'll have more luck with the bottom-up computation, which has `real' natural transformations?
I go on to expand |bu s e g 3|.
The loop in the expression unfolds into a sequence of functions, alternating between table construction using |retabulate| and demolition using |mapBT g|.

`A sequence\ldots'
I mutter.
I didn't expect anything else from unfolding a loop. But the sequential structure is so different from the deeply nested structure of |td|.

And then, something unexpected yet familiar appears in the translated diagram:

\noindent
\begin{minipage}{.45\textwidth}
\begin{code}
bu s e g 3 =  unTip ∘

                mapBT g     ∘
                retabulate  ∘

                mapBT g     ∘
                retabulate  ∘

                mapBT g     ∘
                retabulate  ∘

              mapBT e ∘
              blanks(C 3 0)
\end{code}
\end{minipage}%
\begin{minipage}{.55\textwidth}
\[ \tikzfig{pics/bu} \]
\end{minipage}

There are also two phases for table construction and demolition, and the |g|s and |e| in the demolition phase are \emph{exactly the same} as in |td|!

The string diagram is truly helpful this time.
Now I see, as Richard hinted, that I could rewrite the traditional expression using the naturality of |unTip| and |retabulate| to push |g|~and~|e| to the left of the sequence and separate the two phases:
%if False
\begin{code}
   bu s e g 3
=  {-\;definition -}
   unTip ∘ mapBT g ∘ retabulate ∘ mapBT g CDOTS blanks(C 3 0)
=  {-\;naturality of |unTip| -}
   g ∘ unTip ∘ retabulate ∘ mapBT g CDOTS blanks(C 3 0)
=  {-\;naturality of |retabulate| -}
   g ∘ unTip ∘ mapBT (mapBT g) ∘ retabulate CDOTS blanks(C 3 0)
=  {-\;naturality of |unTip| -}
   g ∘ mapBT g ∘ unTip ∘ retabulate CDOTS blanks(C 3 0)
=  {-\;keep rewriting -}
   g ∘ mapBT (g ∘ mapBT (g ∘ mapBT e)) ∘
   unTip ∘ retabulate ∘ retabulate ∘ retabulate ∘ blanks(C 3 0)
\end{code}
%else
\begin{code}
   bu s e g 3
=  {-\;definition -}
   unTip ∘ mapBT g ∘ retabulate ∘ mapBT g ∘ retabulate ∘ mapBT g ∘ retabulate ∘
   mapBT e ∘ blanks(C 3 0)
=  {-\;naturality of |unTip| -}
   g ∘ unTip ∘ retabulate ∘ mapBT g ∘ retabulate ∘ mapBT g ∘ retabulate ∘
   mapBT e ∘ blanks(C 3 0)
=  {-\;naturality of |retabulate| -}
   g ∘ unTip ∘ mapBT (mapBT g) ∘ retabulate ∘ retabulate ∘ mapBT g ∘ retabulate ∘
   mapBT e ∘ blanks(C 3 0)
=  {-\;naturality of |unTip| again -}
   g ∘ mapBT g ∘ unTip ∘ retabulate ∘ retabulate ∘ mapBT g ∘ retabulate ∘
   mapBT e ∘ blanks(C 3 0)
=  {-\;similarly -}
   g ∘ mapBT g ∘ mapBT (mapBT g) ∘ mapBT (mapBT (mapBT e)) ∘
   unTip ∘ retabulate ∘ retabulate ∘ retabulate ∘ blanks(C 3 0)
=  {-\;functoriality -}
   g ∘ mapBT (g ∘ mapBT (g ∘ mapBT e)) ∘
   unTip ∘ retabulate ∘ retabulate ∘ retabulate ∘ blanks(C 3 0)
\end{code}
%endif
But in the string diagram, all those rewritings amount to nothing more than gently pulling the two phases apart, eventually making the dashed line horizontal.
In fact I don't even bother to pull, because on this diagram I can already see simultaneously both the sequence (the dots appearing one by one vertically) and the result of rewriting the sequence using naturality.

%\todo[inline]{Specialised cases (with a concrete size) only; production and consumption parts, which can be separated by naturality.}

So, modulo naturality, the two algorithms have the same table demolition phase but different table construction phases.
If I can prove that their table construction phases are equal, then (in addition to the parametricity-based proof) I will have another proof that the two algorithms are equal.
For |td|, the construction phase is a right-leaning tree on the diagram, whereas for |bu| it's a left-leaning tree.
Maybe what I need is an equation about |blanks| and |retabulate| that can help me rotate a tree\ldots?
%
\[ \text{\lstinline{cd (choose k xs)}} \equals \text{\lstinline{mapB (flatten . choose k) (choose (k+1) xs)}} \]

The equation flashes through my mind.
Of course it has to be this equation --- I used it as a specification for \lstinline{cd}, the Haskell predecessor of |retabulate|.
How else would I introduce |retabulate| into the picture?
But first let me update this for my dependently typed string diagrams:%
\todo{No need for \lstinline{flatten}}

\[ \tikzfig{pics/rotation} \]

That's a tree rotation all right!
So I should do an induction that uses this equation to rotate the right-leaning tree in |td| and obtain the left-leaning tree in |bu|.
And then I'll need to prove the equation, meaning that I'll need to go through the definitions of |retabulate| and |blanks|\ldots
Oh hell, that's a lot of work.

%\todo[inline]{To prove the equality between |td| and |bu| along this direction:
%The consumption parts of the two algorithms are the same.
%The production parts are left- and right-leaning trees; use the |retabulate|-|blanks| equation (\lstinline{cd}–\lstinline{choose} in Haskell), which is diagrammatically some kind of rotation?
%(Looks like co-associativity; maybe |BT| is some kind of graded comonad?)
%The rotation proof is not difficult but not trivial either, and the |retabulate|-|blanks| equation still needs to be established by delving into the definitions\ldots}

But wait a minute~--- do I really need to go through all this?

The three functors at the top of the diagrams catch my attention.
In Agda, they expand to the type |BT(C n sk) (BT(C sk k) (const ⊤)) xs|.
An inhabitant of this type is a table of \emph{blank} tables, so there is no choice of table entries;
and moreover the structures of all the tables are completely determined by the indices\ldots the type has a unique inhabitant!
So the equation is actually trivial to prove, because, forced by the type, the two sides have to construct the same table, and I don't need to look into the definitions of |retabulate| and |blanks|!

Relieved, I start to work on the proof.
The precise notion I need here is (mere) propositions:
\begin{code}
isProp : Set → Set
isProp a = {x y : a} → x ≡ y
\end{code}
The type |BT(C n k) p xs| is propositional if the payload~|p| is pointwise propositional --- this is easy to prove by a straightforward double induction:
\begin{code}
BT-isProp : (∀ {ys} → isProp (p ys)) → isProp (BT(C n k) p xs)
\end{code}
And then the |rotation| equation can be proved trivially by invoking |BT-isProp| twice:
\Jeremy{alternative line break--- ok?}
\begin{code}
rotation :  retabulate (SUPPRESSED n>k) (blanks(C n k) (SUPPRESSED nGEQk) tt)
              ≡ mapBT (blanks(C sk k) (SUPPRESSED(skGEQk))) (blanks(C n sk) (SUPPRESSED nGEQsk) tt)
rotation = BT-isProp (BT-isProp refl)
\end{code}
All the inequality arguments are universally quantified, but they don't make the proof any more complex, because the proof doesn't look into any of the function definitions.
As long as the type is blank nested tables, the two sides of an equation can be arbitrarily complicated, and I can still prove them equal just by using |BT-isProp|.

Wait, blank nested tables --- aren't those what the construction phases of both algorithms produce?

I face-palm.
It was a waste of time proving the |rotation| equation.
The construction phases of both algorithms produce blank nested tables of the same type --- |BT(C 3 2) (BT(C 2 1) (BT(C 1 0) (const ⊤))) xs| in the concrete examples I tried (|td s e g 3| and |bu s e g 3|).
So I can directly prove them equal using |BT-isProp| three times.
There's no need to do any rotation.

%\todo[inline]{Second climax: the types have already proved the equality between the production parts for us!}

Oh well, at least |rotation| helps to check that the proof idea works before I embark on the general proof that |td| equals |bu|.%
\Josh{|rotation| is also important for understanding the intensional difference between |td| and |bu|, which is a big reason that I try string diagrams despite already having the parametricity-based proof.}
Conceptually I've figured it all out:
Both algorithms have two phases modulo naturality; their table demolition phases are exactly the same, and their table construction phases are equal due to the |BT-isProp| reasoning.
But the general proof is still going to take some work:
If I want to stick to string diagrams, I'll need to translate the algorithms to inductively defined diagrams.
Moreover, the |BT-isProp| reasoning is formally an induction (on the length of the input list), which needs to be worked out.
And actually, compared with a diagrammatic but unformalised proof, I prefer a full Agda formalisation.
That means I'll need to spell out a lot of detail, including naturality rewriting.
Whining, I finish the entire proof in Agda, but as usual, in the end there's a dopamine hit from seeing everything checked.

%\todo[inline]{Sketch inductive diagrammatic definitions and Agda formalisation}

Still, I can't help feeling that I’ve neglected a fundamental aspect of the problem: why the bottom-up algorithm is more efficient.
After making all the effort adopting dependent types and string diagrams, do these state-of-the-art languages help me say something about efficiency too?

String diagrams make it easier for me to see that the table construction phases of both algorithms produce the same layers of tables but in opposite orders.
Only the order used by the bottom-up algorithm allows table construction and demolition to be interleaved, and consequently the algorithm keeps no more than two layers of tables at any time.
That's the crucial difference between the two algorithms.
Now I need to figure out what the difference means algorithmically.

More specifically, why is it good to keep \emph{two} layers of tables and not more?

When there are multiple layers of tables of type |BT(C n k)| with |n > k|, meaning that the input list is split into proper sub-lists multiple times, all the final sub-lists will appear (as indices in the element types) in the entire nested table multiple times --- that is, overlapping sub-problems will appear.
Therefore, when I use~|g| to fill in a nested table, I'm invoking~|g| to compute solutions for overlapping sub-problems repetitively, which is what I want to avoid.
More precisely, `using~|g| to fill in a nested table' means applying~|g| under at least two layers, for example |mapBT (mapBT g) : BT(C 3 2) (BT(C 2 1) (BT(C 1 0) s)) ⇉ BT(C 3 2) (BT(C 2 1) s)|, where the result is at least two layers of tables, so there should be at least \emph{three} layers of tables (to which |mapBT (mapBT g)| is applied) for overlapping sub-problems to occur.
The bottom-up algorithm never gets to three layers of tables, and therefore avoids solving overlapping sub-problems.

That reasoning doesn't sound too bad, although it's clear that there's much more to be done.
The whole argument is still too informal and lacks detail.
It's easy to poke holes in the reasoning --- for example, if the input list has duplicate elements, then the bottom-up algorithm won't be able to avoid solving overlapping sub-problems entirely.
To fix this, the algorithm will need a redesign.
And of course it's tempting to explore more problem-splitting strategies other than immediate sub-lists, maybe eventually arriving at something general about dynamic programming.
All these are for another day, however.%
\todo{need a better ending}

%\todo[inline]{Algorithmically:
%The production parts build the same nested tables but in different orders, and the order used by bottom-up algorithm allows production and consumption to be interleaved.
%Overlapping sub-problems occur in two layers of tables, and they are solved repetitively when |g|~is used to produce two or more layers of tables, which is what the top-down algorithm does after creating deeply nested tables.
%The bottom-up algorithm avoids the repetitive computation because it always uses~|g| to produce only one layer of table.
%(Two layers of tables only appear due to |retabulate|, which only duplicates and redistributes already computed solutions and doesn't recompute them.)}



\section*{Afterword}

\todo[inline]{Largely follows the actual development, which we realise makes a nice story, going from the concrete to the abstract (`based on a true story')}

\todo[inline]{`Socratic monologue' of a dependently typed programmer, going through what they think about (in an intuitive and colloquial style) when solving the problem/mystery (cf~the beginning of the science fiction novel \textit{Project Hail Mary}) rather than reporting a piece of already finished work; the format is more effective for presenting thought processes and focusing on ideas (people don't usually hurry to work out all the technical detail when first solving a problem)}

\todo[inline]{Resist the temptation to generalise (for example, to dynamic programming in general as \citet{Bird-zippy-tabulations} attempted to do), and keep the material simple (no graded comonads, for example) and self-contained (but not a detailed tutorial); loose ends here and there to point out generality and future work (exercises and papers)}

\todo[inline]{Compare with \varcitet{Mu-sublists}{'s} treatment of the problem using simple types and equational reasoning}

\todo[inline]{Why should dependent types, category theory, and string diagrams be in the (mathematically inclined) functional programmer's toolbox?
Explaining, discovering, and proving by writing things down in the right languages.
Specifically:
Fancy types can replace traditional specs and proofs (for example, equality between programs can be proved simply by showing that they have the same, uniquely inhabited type), and are a still under-explored methodology (going beyond length/shape indexing).
Category theory offers useful abstraction (for sometimes comprehending indexed definitions as if they were simply typed); in particular, the categorical abstraction enables the use of string diagrams to make reasoning with naturality transparent (and in this case the main proof is entirely about naturality and rendered trivial).}

\bibliographystyle{ACM-Reference-Format}
\bibliography{bib}

\end{document}
