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

\newcommand{\equals}{\enskip=\enskip}

\let\Bbbk\relax
%include agda.fmt

%format →' = "\kern-.345em\mathrlap{\to}"
%format ∘ = "{\cdot}"
%format ≡ = "{\equiv}"
%format ∈ = "{\in}"
%format [ = "[\kern-2pt"
%format ] = "\kern-2pt]"
%format Σ[ = Σ [

%format (BT'(n)(k)) = BT "^{" n "}_{" k "}"
%format TipZ = Tip "_{\Conid z}"
%format TipS = Tip "_{\Conid s}"

\newcommand{\Var}[1]{\mathit{#1}}

%format a = "\Var a"
%format b = "\Var b"
%format c = "\Var c"
%format e = "\Var e"
%format g = "\Var g"
%format h = "\Var h"
%format k = "\Var k"
%format n = "\Var n"
%format p = "\Var p"
%format x = "\Var x"
%format xs = "\Var xs"
%format ys = "\Var ys"
%format z = "\Var z"

%format sk = 1+ k

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

I stared at the late Richard Bird's `Zippy Tabulations of Recursive Functions'~\citeyearpar{Bird-zippy-tabulations}, frowning.

\begin{lstlisting}
cd                        :: B a -> B (L a)
cd (Bin (Tip a) (Tip b))  =  Tip [a, b]
cd (Bin u (Tip b))        =  Bin (cd u) (mapB (: [b]) u)
cd (Bin (Tip a) v)        =  Tip (a : as) where Tip as = cd v
cd (Bin u v)              =  Bin (cd u) (zipBWith (:) u (cd v))
\end{lstlisting}

I knew \lstinline{B} was this Haskell datatype of trees,
\begin{lstlisting}
data B a = Tip a || Bin (B a) (B a)
\end{lstlisting}
\lstinline{mapB} and \lstinline{zipBWith} were the usual \lstinline{map} and \lstinline{zipWith} functions for these trees, and \lstinline{L} was the standard data type of lists, but how did Richard come up with such an incomprehensible function definition?
And he didn't bother to explain it in the paper.

\section{Simply Typed Algorithms}

Based on what I’d read in the paper, I could make a pretty good guess at what \lstinline{cd} was doing at a high level.

One of the purposes of \citet{Bird-zippy-tabulations} is to study the relationship between top-down and bottom-up algorithms. A generic top-down algorithm is specified by:
\begin{lstlisting}
td :: L X -> Y
td [x]  = f x
td xs   = g . mapF td . dc $ xs
\end{lstlisting}
The input is a list of |X|'s (in \citet{Bird-zippy-tabulations} |L| can be more general, but for our purpose we talk about lists only), and the output is of type |Y|. Singleton lists form the base cases, processed by a function |f :: X -> Y|.
Otherwise, a list can be decomposed into subproblems by a function |dc :: L a -> F (L a)|.
Each |L a| in the |F|-structure is recursively processed by |td|, before |g :: F Y -> Y| combines the results. ...

(in progress...)
\begin{lstlisting}
bu :: L X -> Y
bu = loop . map f
loop [y] = y
loop ys  = loop . map g . cd $ ys
\end{lstlisting}

\todo[inline]{Recap of what Richard's paper wanted to do: transforming a top-down algorithm (which acts as a specification) to a bottom-up algorithm, which `I' (Shin) had already worked out a simplified version; explain why the base cases have to be singleton lists; the role of \lstinline{cd} in the bottom-up algorithm, intuitively; relationship to binomial cofficients}

But I still couldn’t see, \emph{formally}, how to make sense of the definition of \lstinline{cd} or get from the definition to a correctness proof of \lstinline{bu}.%
\todo{Main question; even suggest there's a lot of proving ahead (actually not)}

\section{Indexed Data Types of Binomial Trees}

\todo[inline]{Starting with the legitimacy of \lstinline{zipBWith}, which is now a standard application of length/shape indexing of datatypes --- nothing surprising; opening my favourite editor and switching to Agda}

\begin{code}
data B (a : Set) : ℕ → ℕ → Set where
  TipZ  :   a               → B a       n     0
  TipS  :   a               → B a (1 +  n) (  1 + n)
  Bin   :   B a n (1 +  k)
        →'  B a n       k   → B a (1 +  n) (  1 + k)
\end{code}

\begin{code}
zipBWith : (a → b → c) → B a n k → B b n k → B c n k
\end{code}

\begin{code}
cd : B a n k → B (Vec a (1 + k)) n (1 + k)
\end{code}

\todo[inline]{Use even richer dependent types to say more and prove less}

\todo[inline]{What to say? Need a spec: the equational one using \lstinline{choose} (marking the element positions with sub-lists and specifying where the elements should go); but requires a lot of proving}

\begin{lstlisting}
choose               :: Int -> L a -> B (L a)
choose    0  xs      =  Tip []
choose (k+1) xs      ||  length xs == k+1  =  Tip xs
choose (k+1) (x:xs)  =  Bin (choose (k+1) xs) (mapB (x:) (choose k xs))
\end{lstlisting}

\[ \text{\lstinline{cd (choose k xs)}} \equals \text{\lstinline{mapB (choose k) (choose (k+1) xs)}} \]

\todo[inline]{Maybe find some indexing scheme that enforces the elements of a binomial tree to be \lstinline{mapB h (choose k xs)} with equality proofs about the elements, and then write a function between such trees?
Might be able to turn a large number of equalities into judgemental ones so that the Agda type checker can do the rewriting for us, in the same spirit as \varcitet{McBride-ornaments}{'s} compiler for Hutton's razor; ad~hoc and not very clean however (trees scattered with proofs)}

\todo[inline]{Revelation (before attempting to write down the ad hoc data type): make better use of the dependently typed language by putting the sub-lists in the indices of the element type!}

\begin{code}
data BT {a : Set} : (n k : ℕ) → (Vec a k → Set) → Vec a n → Set where
  TipZ  :   p []                             → BT       n     0       p xs
  TipS  :   p xs                             → BT (1 +  n) (  1 + n)  p xs
  Bin   :   BT n (1 +  k)   p            xs
        →'  BT n       k (  p ∘ (x ∷_))  xs  → BT (1 +  n) (  1 + k)  p (x ∷ xs)
\end{code}

\todo[inline]{The `T' in |BT| stands for `tree' or `table'.
Sometimes write |BT n k| as |(BT' n k)|, mirroring the traditional mathematical notation $C^\mathit{n}_\mathit{k}$ for the number of $k$-combinations of $n$~elements.
Extensionally, |(BT' n k) p xs| means that the predicate |p : Vec a k → Set| holds for all the length-|k| sub-lists of |xs : Vec a n|, or more precisely, a proof of |(BT' n k) p xs| is a table of proofs of |p ys| where |ys| ranges over the length-|k| sub-lists of |xs|.
Both the plain shape-indexed trees and the trees with equality proofs become special cases by specialising |p| to |const a| and |λ ys → Σ[ z ∈ b ] z ≡ h ys| (given |b : Set| and |h : Vec a k → b|).}

\todo[inline]{Apparently there's a design pattern transforming non-deterministic computations into indexed data types to be abstracted and formulated (and a paper to be written).
The continuation-passing-style indexing is also intriguing.
The familiar |All| data type, for example, becomes a special case.}

\todo[inline]{Think of |BT| as a new definition of the notion of combination, and I can now say in terms of |BT| what I wanted to say with the equation involving \lstinline{choose}.
The list in the type of \lstinline{cd}, which is renamed to |retabulate| here, is actually a particular kind of binomial tree.}

\begin{code}
retabulate : n > k → (BT' n k) p xs → (BT' n sk) ((BT' sk k) p) xs
\end{code}
which is parametrically polymorphic in |a : Set| and |p : Vec a k → Set|.

\todo[inline]{First climax: The definition of \lstinline{cd} can be quite straightforwardly ported to to Agda as |retabulate|, meaning that the definition has been verified just by finding a right type for it!
(Need a comparison between \lstinline{cd} and |retabulate|: including more cases than \lstinline{cd} (foreshadowing the generalisation about base cases), generalising a couple of cases, and handling some inequality proofs for the |n > k| argument.)
There's actually no need to understand the definition of \lstinline{cd}/|retabulate|, but I can still work out a case or two to see how well type-directed programming works.
A coherence commuting diagram (in the sense of data refinement) between |retabulate| and \lstinline{cd} to understand one in terms of the other?}

\todo[inline]{Conjecture: the behaviour of |retabulate| is uniquely determined by its type (which works as a tight specification).
The proof may be similar to \varcitet{Voigtlander-BX-for-free}{'s} (and generalised with parametricity for dependent types~\citep{Bernardy-proofs-for-free} and datatype-generic lookup~\citep{Diehl-InfIR}).}

\section{Dependently Typed Algorithms}

\todo[inline]{Do dependent types help us prove that \lstinline{bu} equals \lstinline{td} too?}

\todo[inline]{Starting with the assumptions:
The input to~\lstinline{g} is actually a binomial tree too.
Solutions should be indexed by the input list.
Dependent types allow~|g| to subsume the base cases encoded by~\lstinline{f}.
Arrive at an \emph{induction principle} with induction hypotheses for immediate sub-lists.}

\todo[inline]{Conjecture: the (extensional) behaviour of |td| and |bu| is uniquely determined by their type.
(The induction principle for natural numbers is a simpler example to think about.)
If the conjecture is true, then immediately |td| equals |bu|.
But it's probably going to require a more involved proof using parametricity, which I don't immediately see how to do.
Moreover, I'd like to compare what |td| and |bu| do \emph{intensionally}, an aspect which would be overlooked from the parametricity perspective.
Need more tools to see through the complexity.}

\section{Categories of Families of Types and Functions}

\todo[inline]{One source of complexity is the indices, which are getting annoying and need a bit of management.
In a sense, |retabulate| is still a familiar functional program that transforms a tree of~|p|'s to a tree of trees of~|p|'s, parametrically in~|p|.
Category theory helps us see that and make it precise.
Functional programmers are familiar with types and functions; abstract them as objects and morphisms so that we can specialise them to something new (in this case families of types and functions, or (proof-relevant) predicates and pointwise implications) and work with the new stuff using the same notation and intuition.}

\section{String-Diagrammatic Algorithms}

\todo[inline]{Richard already pointed out that naturality is the key; try string diagrams!}

\todo[inline]{Recap of string diagrams for 2-categories, i.e., layered type structure (composition of functors); layers may be transformed independently of others, and this intuition is captured by the definition of natural transformations.
The two sides of a traditional naturality equation look rather different, whereas in a diagrammatic equation the two sides are `the same picture', allowing us to change perspectives effortlessly.}

\todo[inline]{Specialised cases (with a concrete size) only; production and consumption parts, which can be separated by naturality.
The production parts build the same nested tables but in different orders, and the order used by bottom-up algorithm allows production and consumption to be interleaved.}

\todo[inline]{To prove the equality between |td| and |bu| along this direction:
The consumption parts of the two algorithms are the same.
The production parts are left- and right-leaning trees; use the |retabulate|-|choose| equation, which is diagrammatically some kind of rotation?
(Looks like co-associativity; maybe |BT| is some kind of graded comonad?)
The rotation proof is not difficult but not trivial either, and the |retabulate|-|choose| equation still needs to be established by delving into the definitions\ldots}

\todo[inline]{Second climax: the types have already proved the equality between the production parts for us!}

\todo[inline]{Algorithmically:
Overlapping sub-problems occur in two layers of tables, and they are solved repetitively when |g|~is used to produce two or more layers of tables, which is what the top-down algorithm does after creating deeply nested tables.
The bottom-up algorithm avoids the repetitive computation because it always uses~|g| to produce only one layer of table.
(Two layers of tables only appear due to |retabulate|, which only duplicates and redistributes already computed solutions and doesn't recompute them.)}

\todo[inline]{Sketch inductive diagrammatic definitions and Agda formalisation}

\section*{Afterword}

\todo[inline]{Largely follows the actual development, which we realise makes a nice story, going from the concrete to the abstract (`based on a true story')}

\todo[inline]{Monologue of a dependently typed programmer, going through what they think about (in an intuitive and colloquial style) when solving the problem/mystery (cf~the beginning of the science fiction novel \textit{Project Hail Mary}) rather than reporting a piece of already finished work; the format is more effective for presenting thought processes and focusing on ideas (people don't usually hurry to work out all the technical detail when first solving a problem)}

\todo[inline]{Resist the temptation to generalise, and keep the material simple and self-contained (but not a detailed tutorial); loose ends here and there to point out generality and future work (exercises and papers)}

\todo[inline]{Compare with \varcitet{Mu-sublists}{'s} treatment of the problem using simple types and equational reasoning}

\todo[inline]{Why should dependent types, category theory, and string diagrams be in the (mathematically inclined) functional programmer's toolbox?
Explaining, discovering, and proving by writing things down in the right languages.
Specifically:
Fancy types can replace traditional specs and proofs (for example, equality between programs can be proved simply by showing that they have the same, uniquely inhabited type), and are a still under-explored methodology (going beyond length/shape indexing) --- can work on, e.g., more algorithmic problems (dynamic programming in general)?
Category theory offers useful abstraction (for sometimes comprehending indexed definitions as if they were simply typed); in particular, the categorical abstraction enables the use of string diagrams to make reasoning with naturality transparent (and in this case the main proof is entirely about naturality and rendered trivial).}

\bibliographystyle{ACM-Reference-Format}
\bibliography{bib}

\end{document}
