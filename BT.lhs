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

%\usepackage{mdframed}
%\newenvironment{temp}{\begin{mdframed}[backgroundcolor=red!10, linewidth=0, skipabove=1ex, leftmargin=1ex, rightmargin=0, innerleftmargin=0, innerrightmargin=0, innertopmargin=0, innerbottommargin=0]}{\end{mdframed}}
%\definecolor{SkyBlue}{HTML}{D9F6FF}
%\newenvironment{final}{\begin{mdframed}[backgroundcolor=SkyBlue, linewidth=0, skipabove=1ex, leftmargin=1ex, rightmargin=0, innerleftmargin=0, innerrightmargin=0, innertopmargin=0, innerbottommargin=0]}{\end{mdframed}}

\usepackage{xifthen}
\newcommand{\varcitet}[3][]{\citeauthor{#2}#3~[\ifthenelse{\isempty{#1}}{\citeyear{#2}}{\citeyear[#1]{#2}}]}

\usepackage[inline]{enumitem} % for environment enumerate*

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
\newcommand{\highlight}[2]{\smash{\text{\colorbox{#1}{\kern-.1em\vphantom{\vrule height 1.2ex depth 0.1ex}\smash{\ensuremath{#2}}\kern-.1em}}}}

%format (SUPPRESSED(t)) = "\highlight{suppressed}{" t "}"

\newcommand{\ignorenext}[1]{}

%format (sub(x)) = "\unskip_{" x "}"
%format (C(n)(k)) = "\unskip^{" n "}_{" k "}"
%format CHOOSE (n) (k) = "C^{" n "}_{" k "}"

%format =' = "\unskip=\ignorenext"
%format →' = "\kern-.345em\mathrlap{\to}"
%format ⇉ = "\unskip\rightrightarrows\ignorenext"
%format _⇉_ = _ "{\rightrightarrows}" _
%format ∘ = "\unskip\mathrel\cdot\ignorenext"
%format ⊗ = "\unskip\otimes\ignorenext"
%format ≡ = "\unskip\equiv\ignorenext"
%format ∈ = "\unskip\in\ignorenext"
%format [ = "[\kern-2pt"
%format ] = "\kern-2pt]"
%format Σ[ = Σ [
%format ∀[ = ∀ [
%format ∷_ = ∷ _
%format ᴮᵀ = "_{\Conid{BT}}"
%format ∷ᴮᵀ = ∷ ᴮᵀ
%format _∷ᴮᵀ_ = _ ∷ᴮᵀ _
%format _∷ᴮᵀ = _ ∷ᴮᵀ
%format > = "\unskip>\ignorenext"
%format GEQ = "\unskip\geq\ignorenext"
%format CDOTS = "\cdots"

%format mapBT = map ᴮᵀ
%format zipBTWith = zip ᴮᵀ "\kern-1pt" With
%format blanks' = blanks "^\prime"
%format Fam' = "\text{\textbf{\textsf{Fam}}}"

%format 0 = "\mathrm 0"
%format 1 = "\mathrm 1"
%format 2 = "\mathrm 2"
%format 3 = "\mathrm 3"

\newcommand{\Con}[1]{\mathbf{#1}}

%format bin = "\Con{bin}"
%format refl = "\Con{refl}"
%format tipZ = "\Con{tip_z}"
%format tipS = "\Con{tip_s}"
%format tt = "\Con{tt}"

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
%format e = "\Var e"
%format f = "\Var f"
%format f' = "\Var f^\prime"
%format g = "\Var g"
%format h = "\Var h"
%format k = "\Var k"
%format n = "\Var n"
%format p = "\Var p"
%format q = "\Var q"
%format s = "\Var s"
%format t = "\Var t"
%format u = "\Var u"
%format x = "\Var x"
%format xs = "\Var xs"
%format y = "\Var y"
%format ys = "\Var ys"
%format z = "\Var z"
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
\todo[inline]{Abstract: a demonstration of dependent types and string diagrams for the mathematically inclined functional programmer}
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
cd (Bin (Tip a) (Tip b))  =  Tip [a, b]
cd (Bin u (Tip b))        =  Bin (cd u) (mapB (: [b]) u)
cd (Bin (Tip a) v)        =  Tip (a : as) where Tip as = cd v
cd (Bin u v)              =  Bin (cd u) (zipBWith (:) u (cd v))
\end{lstlisting}

I know \lstinline{B} is this Haskell datatype of trees,
\begin{lstlisting}
data B a = Tip a || Bin (B a) (B a)
\end{lstlisting}
And presumably \lstinline{mapB} and \lstinline{zipBWith} are the usual \lstinline{map} and \lstinline{zipWith} functions for these trees, and \lstinline{L} is the standard data type of lists.
But how did Richard%
\Jeremy{We should be more consistent about whether to call him Richard or Bird. Shin: does it work if we say "Richard" when we refer to the person and say Bird (2008) when we refer to the paper?}
come up with such an incomprehensible function definition?
He didn't bother to explain it in the paper.

\section{Simply Typed Algorithms}

From the explanations that \emph{are} in the paper, I can make a pretty good guess at what \lstinline{cd} is doing at a high level.
%
\citet{Bird-zippy-tabulations} is studying the relationship between top-down and bottom-up algorithms. A generic top-down algorithm is specified by:
%\Josh{Include |f| and |g| as arguments (like |foldr| etc). Shin: Done.}
%\Jeremy{Can we avoid using \lstinline{$}? Richard wouldn't have used it\ldots. Shin: Used application instead.}
\begin{lstlisting}
td :: (X -> Y) -> (L Y -> Y) -> L X -> Y
td f g [x] = f x
td f g xs  = g (map (td f g) (dc xs))
\end{lstlisting}
The input of \lstinline{td} is a list of \lstinline{X}'s, and the output is a single value of type \lstinline{Y}.
Singleton lists form the base cases, processed by a function \lstinline{f :: X -> Y}.
A non-singleton list is decomposed into shorter lists by  \lstinline{dc :: L a -> L (L a)}.
Each shorter list is then recursively processed by \lstinline{td}, before \lstinline{g :: L Y -> Y} combines the results.%
\Josh{\lstinline{F} is initially \lstinline{L} and later \lstinline{B}, but this changes the type of \lstinline{g} too (no need for \lstinline{cvt} etc)? Shin: removed \lstinline{F}. I think we still need \lstinline{cvt} after switching to \lstinline{B}.}
\footnote{The setting in \citet{Bird-zippy-tabulations} is more general: \lstinline{L} need not be a list, and \lstinline{dc} returns an \lstinline{F}-structure of lists. We simplified the setting for ease of discussion.}

\begin{figure}[t]
\centering
\includegraphics[width=0.5\textwidth]{pics/td-call-tree.pdf}
\caption{Computing \lstinline{td "abcd"} top-down.}
\label{fig:td-call-tree}
\end{figure}

In the last ---~and the most difficult~--- example in the paper,
\lstinline{dc :: L a -> L (L a)}%
\Josh{Give definition, which is generalised to \lstinline{choose} later? Shin: done.}
computes all the \emph{immediate sublists} of the given list; that is, all the lists with exactly one element missing:
\begin{lstlisting}
dc [x,y]  = [[x],[y]]
dc (x:xs) = [ x:ys || ys <- dc xs] ++ [xs]
\end{lstlisting}
To compute \lstinline{td "abcd"}, for example, we need to compute \lstinline{td "abc"}, \lstinline{td "abd"}, \lstinline{td "acd"}, and \lstinline{td "bcd"}, as seen in \cref{fig:td-call-tree}.
To compute \lstinline{td "abc"} in turn, we need \lstinline{td "ab"}, \lstinline{td "ac"}, and \lstinline{td "bc"}.
Notice, however, that \lstinline{td "ab"} is invoked again when computing \lstinline{td "abd"}:
following this top-down computation, many sub-computations are repeated.

\begin{figure}[t]
\centering
\includegraphics[width=0.5\textwidth]{pics/sublists-lattice.pdf}
\caption{Computing \lstinline{td "abcde"} bottom-up.
To save space we omitted the \lstinline{td}s.}
\label{fig:sublists-lattice}
\end{figure}

It is better to proceed bottom-up instead, as depicted in Figure~\ref{fig:sublists-lattice}.%
\Josh{Four levels are enough? Shin: I don't understand.. don't we want to see the complete picture?}
The $n$th level
%\Josh{Change to `level' to avoid confusion with `layers of functors' later. Shin: Okay!}
consists of values of \lstinline{td} at lists of length $n$.
We start from level $1$, and compute level $n+1$ from level $n$ by reusing the values stored in the latter, until we reach the top level consisting of only one value.
If the levels are lists, level $2$ would be
\begin{lstlisting}
  [td "ab", td "ac", td "bc", td "ad" ...]
\end{lstlisting}
To construct level $3$ from level $2$, we need a function \lstinline{cd :: L a -> L (L a)} that, given level $2$, copies and rearranges its elements such that the result of \lstinline{td} at immediate sublists of the same list are brought together:
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
bu :: L X -> Y
bu = head . loop . map f

loop [y] = [y]
loop ys  = loop (map g (cd ys))
\end{lstlisting}
That is, level $1$ is obtained by applying \lstinline{f} to each element of the input list. Then we keep applying \lstinline{map g . cd} to get the next level, stopping when we get a level with a single element, which will be our result.

The \lstinline{bu} given above is much simpler than Richard's: to cope with more general problems, he had to store not just values but tables of values in each level.
I'm puzzled at first by why Richard starts from singleton lists instead of the empty list (missing the bottom of the lattice). But then I realise that whereas a $2$-list is completely determined by its two $1$-element sublists, a $1$-list is not determined by its one $0$-element sublist~--- more context would be needed. \Jeremy{\ldots but in Agda, this context can be provided in the type.}

All these, however, are merely a first attempt.
Richard must have realized at some point that it is difficult to define the \lstinline{cd} rearrangement using lists, and decided to represent each level using the \lstinline{B} datatype mentioned before.%
\Josh{Do we get any explanation from the dependently typed reformulation? (Easy access to particular groups of sub-lists?)}
Now \lstinline{cd} has type \lstinline{L a -> B (L a)}, and \lstinline{bu} and \lstinline{loop} are defined by
\begin{lstlisting}
bu :: L X -> Y
bu = unTip . loop . cvt . map f

loop (Tip y) = (Tip y)
loop ys      = loop (mapB g (cd ys))
\end{lstlisting}
where \lstinline{loop :: B Y -> B Y}, and \lstinline{unTip (Tip y) = y}.
The function \lstinline{cvt :: L a -> B a} prepares the first level.%
\Josh{A point of comparison (later we don't need this conversion)}

\begin{figure}[t]
\centering
\includegraphics[width=0.8\textwidth]{pics/map_g_cd.pdf}
\caption{How \lstinline{mapB g . cd} constructs a new level.}
\label{fig:map_g_cd}
\end{figure}

I try to trace Richard's \lstinline{cd} to find out how it works.
Given input \lstinline{"abcde"}, the function \lstinline{cvt} yields a tree that is slanted to the left as level $1$:%
\Josh{Wrong order? Shin: Richard's \lstinline{cvt} is \lstinline{foldl1 Bin . map Tip}.. so it is his order. If that's not consistant with ours... let's think about what to do. :(}
\begin{lstlisting}
Bin (Bin (Bin (Bin (Tip 'a') (Tip 'b')) (Tip 'c')) (Tip 'd')) (Tip 'e')
\end{lstlisting}
Following Richard's convention, I draw a \lstinline{Tip x} as \lstinline{x}, and draw \lstinline{Bin t u} as a dot with \lstinline{t} to its left and \lstinline{u} below, resulting in the tree labelled (1)%
in Figure~\ref{fig:map_g_cd}.
Applying \lstinline{mapB g . cd} to this, I get level $2$, labelled (2) in the figure.
For a closer look, I apply \lstinline{cd} to level $2$.
Indeed, with its clever mapping and zipping, \lstinline{cd} managed to bring together precisely the right elements (labelled (2.5) in Figure~\ref{fig:map_g_cd}), so that when we apply \lstinline{mapB g}, we get level $3$.

This still does not give me much intuition for why \lstinline{cd} works.
Presumably \lstinline{cd} does not do something useful on arbitrary binary trees, only the trees built by \lstinline{cvt} and \lstinline{cd} itself.
What are the constraints on these trees, and how does \lstinline{cd} exploit them?%
\Josh{To be explicitly responded at the end of S3}
Richard did give some hint: if we compute the sizes of subtrees along their left spines (see the red numbers in Figure~\ref{fig:map_g_cd}),
\Jeremy{``Aha!''}
|[1,2,3,4,5]|, |[1,3,6,10]|, and |[1,4,10]| are the first three diagonals of Pascal's triangle --- the trees are related to binomial coefficients! That explains the name \lstinline{B}.%
\Josh{Could be `binary'}

Given these clues, how do we prove that \lstinline{cd} indeed does the job --- bringing related immediate sublists together?
In fact, how do we even write down ``bringing related immediate sublists together'' as a formal specification?
How does that help me to prove that \lstinline{td} equals \lstinline{bu}?
%\Josh{and proving \lstinline{td} equals \lstinline{bu}. Shin: added.}

I fear that there will be plenty of complex proof waiting ahead for me.

%\todo[inline]{Recap of what Richard's paper wanted to do: transforming a top-down algorithm (which acts as a specification) to a bottom-up algorithm, which `I' (Shin) had already worked out a simplified version; explain why the base cases have to be singleton lists; the role of \lstinline{cd} in the bottom-up algorithm, intuitively; relationship to binomial cofficients}

%But I still couldn’t see, \emph{formally}, how to make sense of the definition of \lstinline{cd} or get from the definition to a correctness proof of \lstinline{bu}.
%\todo{Main question; even suggest there's a lot of proving ahead (actually not)}

\section{Indexed Data Types of Binomial Trees}

So, what is \lstinline{cd} doing? As a first step, why is the `zip' justified~--- what if the two trees have different shapes? Ah! Maybe Richard's hint about sizes is key: perhaps the two trees \emph{cannot} have different shapes.

Let me try to prove that, by capturing the tree shape in its type. This is now a standard example in dependent types: familiar territory! I open my favourite editor, and switch from Haskell to Agda.

Here is Richard's \lstinline{B} datatype of binary trees, now indexed by shape:
\Jeremy{For consistency here, we should talk earlier about ``level $k$'' rather than ``level $n$''}
\begin{code}
data B (a : Set) : ℕ → ℕ → Set where
  tipZ  :   a               → B a       n     0
  tipS  :   a               → B a (1 +  n) (  1 + n)
  bin   :   B a n (1 +  k)
        →'  B a n       k   → B a (1 +  n) (  1 + k)
\end{code}
The idea is that the \emph{size} of a tree of type |B a n k| with $0 \le k \le n$ is precisely the binomial coefficient |CHOOSE n k|; and there are no trees of type |B a n k| when $k > n$. Moreover, the indices $n, k$ completely determine the \emph{shape}: there are now two base cases, for $k=0$ and $k=n$, and an inductive case for $0 < k < n$.

This now justifies the zip, which takes two trees \emph{of the same shape}, and returns another tree of that shape:
\begin{code}
zipBWith : (a → b → c) → B a n k → B b n k → B c n k
\end{code}
In fact, that type is so informative that only one program inhabits it, and that program can be found automatically by proof search. (Well, at least the positive clauses are automatic. Proving absurdity of the other clauses takes a little effort.)

And now the type of Richard's \lstinline{cd} can be given more precisely. It takes as input the data for level~$k$ out of $n$ levels, with $0 \le k < n$; these are the results for each of the |CHOOSE n k| length-$k$ sublists of the original length-$n$ list. And it returns as output the components for level~$1+k$; there are |CHOOSE n (sk)| of these, each a length-$(1+k)$ list to be fed into \lstinline{g}. The input data can conveniently be stored in a tree indexed by $n,k$, and the output indexed by $n,1+k$:
\begin{code}
cd : B a n k → B (Vec a (1 + k)) n (1 + k)
\end{code}

So much for the shape. But how do I know that the contents are correct~--- that |cd| is correctly rearranging the values? Perhaps I can use some more refined dependent types, to capture more information intrinsically and leave less for me to prove later.

I need to decide what the types should say~--- that is, I need a specification.
\Jeremy{I don't really understand the TODO: ``What to say? Need a spec: the equational one using \lstinline{choose} (marking the element positions with sub-lists and specifying where the elements should go); but requires a lot of proving''. Update 20240124: A lot of equational reasoning. Do we mention Shin's paper?}
In Haskell, I suppose Richard might have defined the choice of \lstinline{k} elements from a list (implicitly of length \lstinline{n}):
\Jeremy{shouldn't all occurrences of \lstinline{k+1} be \lstinline{1+k}? Update 20240124: it's complicated. Haskell has \lstinline{n+k} patterns; but Agda used to require \lstinline{1+n}.}
\begin{lstlisting}
choose               :: Int -> L a -> B (L a)
choose    0  xs      =  Tip []
choose (k+1) xs      ||  length xs == k+1  =  Tip xs
choose (k+1) (x:xs)  =  Bin (choose (k+1) xs) (mapB (x:) (choose k xs))
\end{lstlisting}
Then he could have specified \lstinline{cd} by
\[ \text{\lstinline{cd (choose k xs)}} \equals \text{\lstinline{mapB (choose k) (choose (k+1) xs)}} \hfill (\ast) \]
Informally: given all the length-\lstinline{k} sublists of length-\lstinline{n} list \lstinline{xs} (with \lstinline{0 <= k < n}), \lstinline{cd} rearranges and duplicates them into the appropriate positions for the length-\lstinline{(k+1)} sublists, where in the position for a particular length-\lstinline{(k+1)} sublist \lstinline{ys} we place all its length-\lstinline{k} sublists \lstinline{choose n ys}.

But proving that using only simple types looks like hard work. Can I find some indexing scheme that forces the elements of a binomial tree to be \lstinline{mapB h (choose k xs)} with equality proofs about the elements, and then write a function between such trees?
I might be able to turn a large number of \Jeremy{propositional?} equalities into judgemental ones so that the Agda type checker can do the rewriting for me, in the same spirit as \varcitet{McBride-ornaments}{'s} compiler for Hutton's Razor. However, that still seems rather ad~hoc, passing proofs by brute force around the tree: not appealing.

A lightbulb lights up over my head: I can make better use of dependent types, by using the sublists themselves as the indices of the element types! After all, nobody said the indices have to be natural numbers. Here is a refinement of the binomial tree datatype:
\begin{code}
data BT {a : Set} : (n k : ℕ) → (Vec a k → Set) → Vec a n → Set where
  tipZ  :   p []                             → BT       n     0       p xs
  tipS  :   p xs                             → BT (1 +  n) (  1 + n)  p xs
  bin   :   BT n (1 +  k)   p            xs
        →'  BT n       k (  p ∘ (x ∷_))  xs  → BT (1 +  n) (  1 + k)  p (x ∷ xs)
\end{code}
The `T' in |BT| stands for `table'.
I decide to write |BT n k| as |BT(C n k)|, mirroring the traditional mathematical notation $C^\mathit{n}_\mathit{k}$ for binomial coefficients.
%format BT_ n k = "\Varid{BT}^{" n "}_{" k "}"
\Jeremy{FWIW, I would define an lhs2\TeX{} macro \verb"BT_" such that \verb"BT_ n k" yields |BT_ n k|.}
Extensionally, |BT(C n k) p xs| means that the predicate |p : Vec a k → Set| holds for all the length-|k| sublists of |xs : Vec a n|; to be more precise, a proof of |BT(C n k) p xs| is a table of proofs of |p ys|, where |ys| ranges over the length-|k| sublists of |xs|.
Both the plain shape-indexed trees and the trees with equality proofs become special cases, by specialising |p| to |const a| and to |λ ys → Σ[ z ∈ b ] z ≡ h ys| (given |b : Set| and |h : Vec a k → b|) respectively.

\todo[inline]{Apparently there's a design pattern to be abstracted and formulated (and a paper to be written) here, transforming non-deterministic computations into indexed data types.
The continuation-passing-style indexing is also intriguing.
The familiar |All| data type, for example, becomes a special case. (For the Afterword?)}

I can think of |BT| as a new definition of the notion of combination, and I can now say in terms of |BT| what I wanted to say with the equation $(\ast)$ involving \lstinline{choose}.
Concretely, I'll use these binomial trees as a data refinement of the lists in the type of \lstinline{cd}; and here's the refinement of `cons':
\begin{code}
_∷ᴮᵀ_ : p xs → BT(C sk k) (p ∘ (x ∷_)) xs → BT(C ssk sk) p (x ∷ xs)
y ∷ᴮᵀ t = bin (tipS y) t
\end{code}
I decide to use the name |retabulate| for the data refinement of \lstinline{cd} \Jeremy{I'd like to think of a better name.}:
\begin{code}
retabulate : (SUPPRESSED(n > k)) → BT(C n k) p xs → BT(C n sk) (BT(C sk k) p) xs
retabulate {xs =' _ ∷ []     }  (tipZ y)  =  tipS  (tipZ y)
retabulate {xs =' _ ∷ _ ∷ _  }  (tipZ y)  =  bin   (retabulate (tipZ y)) (tipZ (tipZ y))
retabulate (bin t         (tipZ y)  )     =  bin   (retabulate t) (mapBT (_∷ᴮᵀ (tipZ y)) t)
retabulate (bin (tipS y)  u         )     =  tipS  (y ∷ᴮᵀ u)
retabulate (bin t         u         )     =  bin   (retabulate t)
                                                   (zipBTWith _∷ᴮᵀ_ t (retabulate u))
\end{code}
This is parametrically polymorphic in the type |a : Set| of list elements and the predicate |p : Vec a k → Set| on sublists.
I have greyed out the |n > k| argument, to indicate that it's in the actual code but omitted in the presentation (for making the comparison with \lstinline{cd} more direct).
\Josh{`Don't bother to trace all the side conditions --- I'll check them in the formalisation.'}
I've also omitted a couple of impossible cases that actually have to be listed and proved absurd.
\Jeremy{The last three cases of |retabulate| obviously match the last three of \lstinline{cd}. But the first two cases of |retabulate| correspond to just the first case of \lstinline{cd}. Evidently we now need an extra case analysis between |tipS| and |bin|; fair enough. But the correspondence would be clearer still if we delegated this case analysis to an auxilliary function, wouldn't it? Update 20240124: first two cases of |retabulate| are different from \lstinline{cd}, because our base case is different}

\todo[inline]{Still need a comparison between \lstinline{cd} and |retabulate|: including more cases than \lstinline{cd} (foreshadowing the generalisation about base cases), generalising a couple of cases, and handling some inequality proofs for the |n > k| argument.
There's actually no need to understand the definition of \lstinline{cd}/|retabulate|, but I can still work out a case or two to see how well type-directed programming works.
A coherence commuting diagram (in the sense of data refinement) between |retabulate| and \lstinline{cd} to understand one in terms of the other?}

I'm pleasantly surprised to see that the definition of \lstinline{cd} can be quite straightforwardly carried over to Agda this way, even with the much more informative type. In fact, the definition has been verified simply by finding the (or rather, a) right type for it!
Further, I conjecture that the behaviour of |retabulate| is uniquely determined by its type, which therefore acts as a tight specification.
The proof might be similar to \varcitet{Voigtlander-BX-for-free}{'s} (and generalised with parametricity for dependent types~\citep{Bernardy-proofs-for-free} and datatype-generic lookup~\citep{Diehl-InfIR}). \Jeremy{Should this move to the Afterword?}

\section{Dependently Typed Algorithms}

So much for \lstinline{cd}, and rearranging the subresults into the correct places. What about the main problem: do dependent types help us prove also that the bottom-up algorithm \lstinline{bu} equals the top-down \lstinline{td}?

Let's start with the assumptions.
The combining function~|g| takes as argument something about the \emph{immediate} sublists of a list: that can be represented as a binomial tree rather than a list too.
The solutions~|s| should be indexed by the input list.
Dependent types allow~|g| to subsume the base cases encoded separately by~\lstinline{f} in Richard's paper.
We can also use the more obvious empty list as the base case, rather than having to stop with singleton lists, because the missing context is provided in the type.
We arrive at an \emph{induction principle} for lists, in which the induction hypothesis is that the property holds for all immediate sublists:
\Jeremy{Why are the two |⊤| arguments needed? What breaks if we try to do without them? Could we then also do without the distinction between |blanks| and |blanks'|?}
\begin{code}
ImmediateSublistInduction : Set₁
ImmediateSublistInduction =
  {  a : Set} (s : {k : ℕ} → Vec a k → Set)
  (  e : {ys : Vec a 0} → ⊤ → s ys)
  (  g : {k : ℕ} {ys : Vec a (1 + k)} → BT(C sk k) s ys → s ys)
  (  n : ℕ) {xs : Vec a n} → ⊤ → s xs
\end{code}
That is, we can prove a property~|s| for a given list~|xs| of length~|n|, given a base case proof~|e| for the empty list, and an inductive step~|g| assuming the property for all immediate sublists of a nonempty list.

Here's the top-down algorithm:
\begin{code}
td : ImmediateSublistInduction
td s e g    0      = e
td s e g (  1+ n)  = g ∘ mapBT (td s e g n) ∘ blanks(C sn n)
\end{code}
This is appealingly similar to Richard's function~\lstinline{td}, the only significant difference being the freedom to use the empty list for the base case.
Here, |blanks(C n k)| constructs the length-|k| sublists of a length-|n| list:
\Jeremy{I suggest calling this |choose| instead of |blanks|. And it would be helpful to go first to the version returning a |BT(C n k) id xs|, then noticing that the sublists aren't needed in the value because they are completely determined by the types.}
\begin{code}
blanks' : (n k : ℕ) → (SUPPRESSED(n GEQ k)) → BT(C n k) (const ⊤) xs
blanks' _          0       = tipZ tt
blanks' (1 + k) (  1 + k)  = tipS tt
blanks' (1 + n) (  1 + k)  = bin (blanks' n (1 + k)) (blanks' n k)

blanks : (n k : ℕ) → (SUPPRESSED(n GEQ k)) → ⊤ → BT(C n k) (const ⊤) xs
blanks(C n k) = const (blanks' n k)
\end{code}
And here is the bottom-up algorithm:
\Jeremy{missing a definition of |unTip|?}
\begin{code}
bu : ImmediateSublistInduction
bu s e g n = unTip ∘ loop 0 ∘ mapBT e ∘ blanks(C n 0)
  where
    loop : (k : ℕ) → (SUPPRESSED(k ≤ n)) → BT(C n k) s xs → BT(C n n) s xs
    loop n  = id
    loop k  = loop (1 + k) ∘ mapBT g ∘ retabulate
\end{code}
That is, we initialize with a proof for the empty list, and iteratively lift this to all longer and longer sublists of the input.

Intriguingly, any two inhabitants of |ImmediateSublistInduction| are equal (up to extensional equality), due to parametricity\Jeremy{proof?}. So in fact |td| equals |bu|, merely because they have the same, uniquely inhabited type!
(The induction principle for natural numbers is a simpler example to think about.)Jeremy{``I'm reminded of a cute recent paper by Olivier Danvy [JFP 29:e26, 2019] about left and right folds over the natural numbers, which is a simpler illustration of the same idea.'' Fair?})

But I would really like to compare what |td| and |bu| do \emph{intensionally}. That aspect is overlooked from the parametricity perspective. I'll need some more powerful tools to see through the extra complexity\ldots

\section{Categories of Families of Types and Functions}

All the indices in the types are getting annoying, and they are distorting the types to the extent that makes me afraid that I've deviated too much from Richard's paper.
Have I taken a completely new path?
That would be exciting, but also frightening because I'd be on my own and couldn't rely on Richard's insights anymore.

I've definitely done something radically new that Richard wouldn't imagine: proving two non-trivial programs equal just by saying that they have the same type.
On the other hand, I don't think I'm in a totally uncharted territory yet, because I still see vaguely familiar patterns if I squint at my Agda code:
The programs are still essentially the same as their Haskell counterparts; in particular, like \lstinline{cd}, my |retabulate| still transforms a tree of |p|'s into a tree of lists/trees of |p|'s, roughly speaking.

Hm, does it even make sense to say `a tree of |p|'s'?
Usually when a functional programmer says `a tree of something', that `tree' is a parametric data type, and that `something' is a type, but here |p|~is a type family rather than a type\ldots

And then I see it: \emph{I'm in a different category.}

Functional programmers are familiar with types and functions, and knows when functions can be composed sequentially --- when adjacent functions are mediated by the same types.
Categories are settings in which the same intuition about sequential composition works:
Instead of types and functions, the categorical programmer can switch to work with some \emph{objects} and \emph{morphisms} specified by a category, where each morphism is labelled with a source object and a target object (like the source and target types of a function), and morphisms can be composed sequentially when adjacent morphisms are mediated by the same objects.%
\todo{laws}
Working in a new setting that's identified as a category (or some crazier variant that supports more operations in addition to sequential composition) is a blessing for the functional programmer: It means that the programmer can still rely on some of their intuitions about types and functions to navigate in the new setting.
(And the formal definitions of various kinds of category makes it precise what intuitions remain reliable.)

In my case, I've left the category of types and functions and landed in a kind of category where the objects are type families.
A bit of notation will make it clearer:
\begin{code}
Fam : Set → Set₁
Fam a = a → Set
\end{code}
Now I can write
\begin{code}
BT(C n k) : Fam (Vec a k) → Fam (Vec a n)
\end{code}
This makes a lot of sense:
In a simply typed setting, a parametric data type~|D| maps a type~|a| to a type |D a|; categorically, it should map an object to an object, and indeed |BT(C n k)| maps a type family to a type family.

\todo[inline]{Explain the relationship between parametric data types and functors; independence of data at functor level from those at parameter level (foreshadowing natural transformations?)}

What about morphisms?
A clue can be found in the type of the standard function |map(sub D) : (a → b) → (D a → D b)| that comes with any (`reasonable') parametric data type~|D| for changing the type parameter.
Looking through the categorical lens, |map(sub D)| takes a morphism/function from~|a| to~|b| and maps it to a morphism/function from |D a| to |D b|.
Then it is obvious from
\begin{code}
mapBT : (∀ {ys} → p ys → q ys) → ∀ {xs} → BT(C n k) p xs → BT(C n k) q xs
\end{code}
that the morphisms of the kind of category I'm in should be families of functions,
\begin{code}
_⇉_ : Fam a → Fam a → Set
p ⇉ q = ∀ {x} → p x → q x
\end{code}
so that the type of |mapBT| can be rewritten into the familiar form --- just like the type of |map(sub D)|:
\begin{code}
mapBT : (p ⇉ q) → (BT(C n k) p ⇉ BT(C n k) q)
\end{code}

There are quite a few versions of `categories of families', and the version I'm looking at is a simplest one:
Given an index type~|a|, a category of families has objects of type |Fam a| and morphisms between objects |p|~and~|q| of type |p ⇉ q| --- I'll call such a category |Fam' a|.
So actually I'm working in not just one but many categories of families with different index types.
For example, |BT(C n k)| (together with |mapBT|), as a functor, goes from |Fam' (Vec a k)| to |Fam' (Vec a n)|.
But I'd better check if all the other functions used in the two algorithms fit into these categories.
Sure enough:
\begin{code}
retabulate     :  BT(C n k) p   ⇉  BT(C n sk) (BT(C sk k) p)
unTip          :  BT(C n n) p   ⇉  p
blanks(C n k)  :  const ⊤       ⇉  BT(C n k) (const ⊤)
g              :  BT(C sk k) s  ⇉  s
e              :  const ⊤       ⇉  s
\end{code}
where the |⊤|~arguments of |blanks| and~|e| need to be lifted to a type family |const ⊤| to fit into the category of families.
The usual side conditions apply (|n > k| for |retabulate| and |n GEQ k| for |blanks(C n k)|), and |e|~is defined only in |Fam' (Vec a 0)|.

\todo[inline]{Not a purely categorical treatment, but just using categories as an abstraction that highlights certain structures of the programs}

%\todo[inline]{One source of complexity is the indices, which are getting annoying and need a bit of management.
%In a sense, |retabulate| is still a familiar functional program that transforms a tree of~|p|'s to a tree of trees of~|p|'s, parametrically in~|p|.
%Category theory helps us see that and make it precise.
%Functional programmers are familiar with types and functions; abstract them as objects and morphisms so that we can specialise them to something new (in this case families of types and functions, or (proof-relevant) predicates and pointwise implications) and work with the new stuff using the same notation and intuition.
%In particular, |BT(C n k)| is a real functor, just in the new categories, and |mapBT| is the functorial map.}

\section{String-Diagrammatic Algorithms}

Now I see that I'm pretty much still writing ordinary functional programs, so there's a better chance that I can port what Richard did with his programs to my setting.
An important clue left by Richard was \emph{naturality}, a categorical notion which he used a lot in his proofs.
In functional programming, naturality usually stems from parametricity:
All parametric functions (such as |retabulate| and |unTip|) are \emph{natural transformations}.
Now I know in which categories I should talk about them.

And I know a new weapon that Richard didn't know: \emph{string diagrams}.
I've seen how dramatically string diagrams simplify proofs about natural transformations (and other stuff too, for which the simplification is even more dramatic actually), so it's probably worthwhile to take a look at the two algorithms from a string-diagrammatic perspective.

But before that, I need to refresh my memory of string diagrams\ldots

%\todo[inline]{Richard already pointed out that naturality is the key; try string diagrams!}

At a higher abstraction level, what a natural transformation does is transform one functor into another.
For example, |retabulate| transforms the functor |BT(C n k)| into the composition of functors |BT(C n sk) ∘ BT(C sk k)|, while |unTip| transforms the functor |BT(C n n)| into the identity functor.
String diagrams reorganise such `type information' in two-dimensional pictures:
Natural transformations are represented as dots with input wires attached below and output wires above, where the wires represent functors.
(I learned string diagrams mainly from \citet{Coecke-PQP}, so my string diagrams go upwards from input to output.)
\[ \tikzfig{pics/retabulate-unTip} \]
The composition of a series of functors is represented as a bunch of wires spread horizontally, and the identity functor is omitted (being the unit of functor composition), so |retabulate| has two output wires and |unTip| has none.

Any two natural transformations |α : ∀ {a} → F a → G a| and |β : ∀ {a} → G a → H a| can be composed \emph{sequentially} into |β ∘ α : ∀ {a} → F a → H a|, which is drawn on a string diagram as |α|~and~|β| connected by the middle wire with label~|G| (which obscures part of the wire);
|α|~can also be composed \emph{in parallel} with |α' : ∀ {b} → F' b → G' b| into |α ⊗ α' : ∀ {b} → F (F' b) → G (G' b)|, which is drawn on a string diagram as, well, |α|~and~|α'| in parallel.
\[ \tikzfig{pics/vertical} \hspace{.15\textwidth} \tikzfig{pics/horizontal} \]
The two kinds of composition embody the two-dimensional structure of natural transformations:
Natural transformations are laid out vertically in the order they are applied.
Independent of that order/direction/dimension, the functors being transformed have a composite structure, which is intuitively layers of functors that can be transformed individually without affecting other layers --- that is, in parallel.
These layers are laid out horizontally.

To see why the two-dimensional layout is helpful, consider two ways of defining |α ⊗ α'|: either |map(sub G) α' ∘ α|, where the outer functor~|F| is transformed to~|G| first, or |α ∘ map(sub F) α'|, where the inner functor~|F'| is transformed to~|G'| first.
The two definitions are equal (due to the naturality of~|α|), but the equality can be seen more directly with string diagrams:
\[ \tikzfig{pics/horizontal-definitions} \]
On the diagrams, |α'|~is applied to the inner/right wire because |map α'| means skipping over the outer/left functor and transforming the inner functor using~|α'|.
(The dashed lines are added to emphasise that both diagrams are constructed as the sequential composition of two transformations.)
By laying out layers of functors in a separate dimension, it's much easier to see which layers are being transformed, and determine whether two sequentially composed transformations are in fact applied in parallel, so that their order of application can be swapped.
This is abstracted as a diagrammatic reasoning principle:
Dots can be moved upwards or downwards, possibly changing their vertical positions relative to other dots (while stretching or shrinking the wires, which can be thought of as elastic strings), and the meaning of a diagram will remain the same (extensionally).

There are many functions that are not natural transformations, but they can be lifted to natural transformations to fit into string diagrams:
A function |f : a → b| can be lifted to have the type |∀ {c} → (const a) c → (const b) c| (where |c|~can range over any non-empty domain) and become a natural transformation from |const a| to |const b|.
I prefer to leave the lifting implicit and just write |a|~and~|b| for wire labels, since it's usually clear that |a|~and~|b| are not functors and need to be lifted.
For some concrete examples, here are the types of the rest of the functions used in the two algorithms as string diagrams:
\[ \tikzfig{pics/g-e-blanks} \]
(Here |⊤|~abbreviates the type family |const ⊤|, which is only an object in the categories of families, and needs to be lifted to |const (const ⊤)| to be a functor for those categories.)%
\todo{Faces are categories?}
With the lifting, the usual naturality can also be reformulated diagrammatically:
For any |f : a → b|,
\[ |map(sub G) f ∘ α = α ∘ map(sub F) f| \hspace{.15\textwidth} \tikzfig{pics/naturality} \]
The reformulation makes it intuitive that the naturality of~|α| is about |α|~transforming only the outer functor, independently of whatever happening inside.

%\todo[inline]{Recap of string diagrams for 2-categories, i.e., layered type structure (composition of functors); layers may be transformed independently of others, and this intuition is captured by the definition of natural transformations.
%The two sides of a traditional naturality equation look rather different, whereas in a diagrammatic equation the two sides are `the same picture', allowing us to change perspectives effortlessly.}

That's enough abstract nonsense --- time to get back to the two algorithms.
I'm not confident enough to work with the recursive definitions straight away, so I take the special case |td s e g 3| of the top-down computation and unfolds it into a deeply nested expression.
Translating that into a string diagram is basically writing down all the intermediate type information and laying out the nested type structures horizontally (whereas function composition is laid out vertically).

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

All the |mapBT|'s are gone in the diagram, because I can directly apply a transformation to the intended layers/wires, rather than count awkwardly how many outer layers I want to skip using |mapBT|, one layer at a time.
Functoriality (|mapBT (f' ∘ f) = mapBT f' ∘ mapBT f|) is also transparent in the diagram, so it's slightly easier to see that |td| has two phases (between which I draw a dashed line):
The first phase constructs deeply nested blank tables, and the second phase fills and demolishes the tables inside out.

It doesn't seem that the string diagram helps much though.
Functoriality is already somewhat transparent in the traditional expression (thanks to the infix notation of function composition), so I don't really need the string diagram to see that |td| has two phases.
Moreover, there's nothing I can meaningfully move in the diagram --- all the transformations here are lifted after all.

Hm, maybe I'll have more luck with the bottom-up computation, which has `real' natural transformations?
I go on to expand |bu s e g 3|.
The loop in the expression unfolds into a sequence of functions, alternating between table construction using |retabulate| and demolition using |mapBT g|.

`A sequence\ldots'
I mutter.
I don't expect anything else from unfolding a loop, but the sequential structure is so different from the deeply nested structure of |td|.

And then, something unexpected yet familiar appears in the translated diagram.

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

There are also two phases for table construction and demolition, and the demolition phase is \emph{exactly the same} as the one in |td|!

The string diagram is truly helpful this time.
Now I see that, as Richard hinted, I could rewrite the traditional expression using the naturality of |unTip| and |retabulate| to push |g|~and~|e| to the left of the sequence and separate the two phases:
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
But on the string diagram, all those rewritings amount to nothing more than gently pulling the two phases apart from each other (making the dashed line horizontal).
In fact I don't even bother to pull, because on this diagram I can already see both the sequence (the dots appearing one by one vertically) and the result of rewriting the sequence using naturality at the same time.

%\todo[inline]{Specialised cases (with a concrete size) only; production and consumption parts, which can be separated by naturality.}

So, modulo naturality, the two algorithms have the same table demolition phase but different table construction phases.
If I can prove that their table construction phases are equal, then (in addition to the parametricity-based proof) I will have another proof that the two algorithms are equal.
For |td|, the construction phase is a right-leaning tree on the diagram, whereas for |bu| it's a left-leaning tree.
Maybe what I need is an equation about |blanks| and |retabulate| that can help me rotate a tree\ldots?
%
\[ \text{\lstinline{cd (choose k xs)}} \equals \text{\lstinline{mapB (choose k) (choose (k+1) xs)}} \]

The equation flashes through my mind.
Of course it has to be this equation --- I used it as a specification for \lstinline{cd}, the Haskell predecessor of |retabulate|.
How else would I introduce |retabulate| into the picture?
But first let me update this to a dependently typed string diagram.

\[ \tikzfig{pics/rotation} \]

That's a tree rotation all right.
So I should do an induction that uses this equation to rotate the right-leaning tree in |td| and obtain the left-leaning tree in |bu|.
And then I'll need to prove the equation, meaning that I'll need to go through the definitions of |retabulate| and |blanks|\ldots
Oh hell, that's a lot of work.

%\todo[inline]{To prove the equality between |td| and |bu| along this direction:
%The consumption parts of the two algorithms are the same.
%The production parts are left- and right-leaning trees; use the |retabulate|-|blanks| equation (\lstinline{cd}–\lstinline{choose} in Haskell), which is diagrammatically some kind of rotation?
%(Looks like co-associativity; maybe |BT| is some kind of graded comonad?)
%The rotation proof is not difficult but not trivial either, and the |retabulate|-|blanks| equation still needs to be established by delving into the definitions\ldots}

But do I need to?

The three functors at the top of the diagrams catch my attention.
In Agda, they expand to the type |BT(C n sk) (BT(C sk k) (const ⊤)) xs|.
An inhabitant of this type is a table of \emph{blank} tables, and the structures of all the tables are completely determined by the indices --- the type has a unique inhabitant!
So the equation is actually trivial to prove, because, forced by the type, the two sides have to construct the same table, and I don't need to look into the definitions of |retabulate| and |blanks|!

Relieved, I start to work on the proof.
The precise notion I need here is (mere) propositions.
\begin{code}
isProp : Set → Set
isProp a = {x y : a} → x ≡ y
\end{code}
The type |BT(C n k) p xs| is propositional if the payload~|p| is pointwise propositional --- this is easy to prove by a straightforward double induction.
\begin{code}
BT-isProp : (∀ {ys} → isProp (p ys)) → isProp (BT(C n k) p xs)
\end{code}
And then the |rotation| equation can be proved trivially by invoking |BT-isProp| twice.
\begin{code}
rotation  :
  retabulate (SUPPRESSED n>k) (blanks(C n k) (SUPPRESSED nGEQk) tt) ≡ mapBT (blanks(C sk k) (SUPPRESSED(skGEQk))) (blanks(C n sk) (SUPPRESSED nGEQsk) tt)
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
Whining, I finish the entire proof in Agda, but as usual, in the end it's satisfying to see everything checked.

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
More precisely, `using~|g| to fill in a nested table' means applying~|g| under at least two layers, for example |mapBT (mapBT g) : BT(C 3 2) (BT(C 2 1) (BT(C 1 0) s)) ⇉ BT(C 3 2) (BT(C 2 1) s)|, where the result is at least two layers of tables, so there should be at least \emph{three} layers of tables (to which |mapBT (mapBT g)| is applied) for the solving of overlapping sub-problems to happen.
The bottom-up algorithm never gets to three layers of tables, and therefore avoids solving overlapping sub-problems.

That reasoning doesn't sound too bad, although it's clear that there's much more to be done.
The whole reasoning is still too informal and lacks detail.
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
