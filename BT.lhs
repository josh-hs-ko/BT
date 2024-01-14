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

%format =' = "\unskip=\ignorenext"
%format →' = "\kern-.345em\mathrlap{\to}"
%format ⇉ = "\unskip\rightrightarrows\ignorenext"
%format ∘ = "{\cdot}"
%format ≡ = "{\equiv}"
%format ∈ = "{\in}"
%format [ = "[\kern-2pt"
%format ] = "\kern-2pt]"
%format Σ[ = Σ [
%format ∀[ = ∀ [
%format ∷_ = ∷ _
%format ᴮᵀ = "_{\Conid{BT}}"
%format ∷ᴮᵀ = ∷ ᴮᵀ
%format _∷ᴮᵀ_ = _ ∷ᴮᵀ _
%format _∷ᴮᵀ = _ ∷ᴮᵀ
%format GEQ = "\unskip\geq\ignorenext"

%format mapBT = map ᴮᵀ
%format TipZ = Tip "_{\Conid z}"
%format TipS = Tip "_{\Conid s}"
%format zipBTWith = zip ᴮᵀ With
%format blanks' = blanks "^\prime"

%format 0 = "\mathrm 0"
%format 1 = "\mathrm 1"
%format 2 = "\mathrm 2"
%format 3 = "\mathrm 3"

\newcommand{\Var}[1]{\mathit{#1}}

%format F = "\Var F"
%format G = "\Var G"
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

%format sn = 1 + n
%format sk = 1 + k
%format ssk = 2 + k

%format n>k = n > k
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
\lstinline{mapB} and \lstinline{zipBWith} are the usual \lstinline{map} and \lstinline{zipWith} functions for these trees, and \lstinline{L} is the standard data type of lists, but how did Richard come up with such an incomprehensible function definition?
And he didn't bother to explain it in the paper.

\section{Simply Typed Algorithms}

Based on what I’ve read in the paper, I can make a pretty good guess at what \lstinline{cd} is doing at a high level.
%
\citet{Bird-zippy-tabulations} is a study of the relationship between top-down and bottom-up algorithms. A generic top-down algorithm is specified by:
\begin{lstlisting}
td :: L X -> Y
td [x]  = f x
td xs   = g . mapF td . dc $ xs
\end{lstlisting}
In \citet{Bird-zippy-tabulations} \lstinline{L} can be more general, but for our purpose we talk about lists only.
Therefore, the input is a list of \lstinline{X}'s and the output is of type \lstinline{Y}.
Singleton lists form the base cases, processed by a function \lstinline{f :: X -> Y}.
A non-empty list is decomposed into an \lstinline{F}-structure of lists by  \lstinline{dc :: L a -> F (L a)}.
Each \lstinline{L a} is then recursively processed by \lstinline{td}, before \lstinline{g :: F Y -> Y} combines the results.

In the last, and the most difficult example in \citet{Bird-zippy-tabulations},
\lstinline{F = L}, and \lstinline{dc :: L a -> L (L a)} computes all the \emph{immediate sublists} of the given list, that is, all the lists with exactly one element missing.
To compute \lstinline{td "abcd"}, for example, we need to compute \lstinline{td "abc"}, \lstinline{td "abd"}, \lstinline{td "acd"}, and \lstinline{td "bcd"}.
To compute \lstinline{td "abc"}, in turns, we need \lstinline{td "ab"}, \lstinline{td "ac"}, and \lstinline{td "bc"}.
Notice that \lstinline{td "ab"} will also be invoked when computing \lstinline{td "abd"} --- proceeding in this top-down manner, many sub-computation are repeated.

One would instead wish to proceed in a bottom-up manner, depicted in Figure TODO.
The $n$th layer consists of values of \lstinline{td} at lists of length $n$.
We wish to start from layer $1$, and compute layer $n+1$ from layer $n$ by reusing the values stored in the latter, until we reach a layer consisting of only one value.
Assuming, for now, that each layer is represented by lists.
Layer $2$ would be
\begin{lstlisting}
  [td "ab", td "ac", td "bc", td "ad" ...]
\end{lstlisting}
To construct layer $3$ from layer $2$, we wish to have a function \lstinline{cd :: L a -> L (L a)} that, given layer $2$, copies and rearranges its elements such that immediate sublists of the same list are brought together:
\begin{lstlisting}
  [[td "ab", td "ac", td "bc"], [td "ab", td "ad", td "bd"] ... ]
\end{lstlisting}
Applying \lstinline{map g} to the list above, we get layer $3$:
\begin{lstlisting}
  [td "abc", td "abd", td "acd", td "bcd" ...]
\end{lstlisting}
If such a function \lstinline{cd} can be constructed, an alternative bottom-up algorithm is given by:
\begin{lstlisting}
bu :: L X -> Y                loop [y] = y
bu = loop . map f             loop ys  = loop . map g . cd $ ys
\end{lstlisting}
That is, layer $1$ is constructed by applying \lstinline{f} to each element of the input list. Afterwards, we keep applying \lstinline{map g . cd} to get the next level, until we get a layer with only one element, which will be our result.

All these, however, are merely for giving us some intuition.
Richard must have realized at some point that it is difficult to construct \lstinline{cd} using lists, and decided to represent each level using the \lstinline{B} datatype mentioned before.
Therefore \lstinline{cd} has type \lstinline{L a -> B (L a)}, and \lstinline{loop} is defined by
\begin{lstlisting}
loop (Tip y) = y
loop ys      = loop . mapB g . cd $ ys
\end{lstlisting}

A lot remain unanswered.
How do we know that \lstinline{cd}, whose definition was given by Richard without explanation, indeed does the job --- bringing related immediate sublists together?
How do we even write down ``bringing related immediate sublists together'' as a formal specification?
The datatype \lstinline{B} is more than it seems: \lstinline{cd} does not generate all trees, but only those meeting certain constraints.
What are the constraints, and how does \lstinline{cd} exploit them to do its job?

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
Sometimes write |BT n k| as |BT(C n k)|, mirroring the traditional mathematical notation $C^\mathit{n}_\mathit{k}$ for the number of $k$-combinations of $n$~elements.
Extensionally, |BT(C n k) p xs| means that the predicate |p : Vec a k → Set| holds for all the length-|k| sub-lists of |xs : Vec a n|, or more precisely, a proof of |BT(C n k) p xs| is a table of proofs of |p ys| where |ys| ranges over the length-|k| sub-lists of |xs|.
Both the plain shape-indexed trees and the trees with equality proofs become special cases by specialising |p| to |const a| and |λ ys → Σ[ z ∈ b ] z ≡ h ys| (given |b : Set| and |h : Vec a k → b|).}

\todo[inline]{Apparently there's a design pattern transforming non-deterministic computations into indexed data types to be abstracted and formulated (and a paper to be written).
The continuation-passing-style indexing is also intriguing.
The familiar |All| data type, for example, becomes a special case.}

\todo[inline]{Think of |BT| as a new definition of the notion of combination, and I can now say in terms of |BT| what I wanted to say with the equation involving \lstinline{choose}.
The list in the type of \lstinline{cd}, which is renamed to |retabulate| here, is actually a particular kind of binomial tree.}

\begin{code}
_∷ᴮᵀ_ : p xs → BT(C sk k) (p ∘ (x ∷_)) xs → BT(C ssk sk) p (x ∷ xs)
y ∷ᴮᵀ t = Bin (TipS y) t
\end{code}

\begin{code}
retabulate : (SUPPRESSED(n > k)) → BT(C n k) p xs → BT(C n sk) (BT(C sk k) p) xs
retabulate {xs =' _ ∷ []     }  (TipZ y)  =  TipS  (TipZ y)
retabulate {xs =' _ ∷ _ ∷ _  }  (TipZ y)  =  Bin   (retabulate (TipZ y)) (TipZ (TipZ y))
retabulate (Bin t         (TipZ y)  )     =  Bin   (retabulate t) (mapBT (_∷ᴮᵀ (TipZ y)) t)
retabulate (Bin (TipS y)  u         )     =  TipS  (y ∷ᴮᵀ u)
retabulate (Bin t         u         )     =  Bin   (retabulate t)
                                                   (zipBTWith _∷ᴮᵀ_ t (retabulate u))

\end{code}
which is parametrically polymorphic in |a : Set| and |p : Vec a k → Set|.

\todo[inline]{The |n > k| argument is `greyed out', meaning that it's in the actual code but omitted in the presentation (for comparing with \lstinline{cd} more easily).
Also omitted are a couple of impossible cases that actually have to be listed and proved to be impossible.}

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

\begin{code}
blanks' : (n k : ℕ) → (SUPPRESSED(n GEQ k)) → BT(C n k) (const ⊤) xs
blanks' _          0       = TipZ tt
blanks' (1 + k) (  1 + k)  = TipS tt
blanks' (1 + n) (  1 + k)  = Bin (blanks' n (1 + k)) (blanks' n k)

blanks : (n k : ℕ) → (SUPPRESSED(n GEQ k)) → ⊤ → BT(C n k) (const ⊤) xs
blanks(C n k) = const (blanks' n k)
\end{code}

\begin{code}
ImmediateSublistInduction : Set₁
ImmediateSublistInduction =
  {  a : Set} (s : {k : ℕ} → Vec a k → Set)
  (  e : {xs : Vec a 0} → ⊤ → s xs)
  (  g : {k : ℕ} {xs : Vec a (1 + k)} → BT(C sk k) s xs → s xs)
  (  n : ℕ) {xs : Vec a n} → ⊤ → s xs
\end{code}

\begin{code}
td : ImmediateSublistInduction
td s e g    0      = e
td s e g (  1+ n)  = g ∘ mapBT (td s e g n) ∘ blanks(C sn n)
\end{code}

\begin{code}
bu : ImmediateSublistInduction
bu s e g n = unTip ∘ loop 0 ∘ mapBT e ∘ blanks(C n 0)
  where
    loop : (k : ℕ) → (SUPPRESSED(k ≤ n)) → BT n k s xs → BT n n s xs
    loop n  = id
    loop k  = loop (1 + k) ∘ mapBT g ∘ retabulate
\end{code}

\todo[inline]{Any two inhabitants of |ImmediateSublistInduction| are equal (up to extensional equality) due to parametricity, so |td| equals |bu| simply because they have the same, uniquely inhabited type.
(The induction principle for natural numbers is a simpler example to think about.)
However, I'd like to compare what |td| and |bu| do \emph{intensionally}, an aspect which would be overlooked from the parametricity perspective.
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

If naturality is the key, then drawing the two algorithms as string diagrams should save me the trouble of naturality rewriting.

Not confident enough to work with the recursive definitions straight away, I take the special case |td s e g 3| of the top-down computation and unfolds it into a deeply nested expression.
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
\[ \tikzfig{td} \]
\end{minipage}

All the |mapBT|'s are gone in the diagram, because I can directly apply a function to the intended layers/wires, rather than count awkwardly how many outer layers I want to skip using |mapBT|, one layer at a time.
Functoriality (|mapBT (f ∘ f') =' mapBT f ∘ mapBT f'|) is also transparent in the diagram, so now it's slightly easier to see that |td| has two phases (between which I draw a dashed line):
The first phase constructs deeply nested blank tables, and the second phase fills and demolishes the tables inside out.

It doesn't seem that the string diagram helps much though.
Functoriality is already more or less transparent in the traditional expression (thanks to the infix notation of function composition), so I don't really need the string diagram to see that |td| has two phases.
Moreover, there's nothing I can move around in the diagram --- nothing in the diagram is a real natural transformation.

Somewhat suspiciously, I turn to the bottom-up computation |bu s e g 3|.
The loop in the expression unfolds into a sequence of functions, alternating between table construction using |retabulate| and demolition using |mapBT g|.

`A sequence\ldots'
I mutter.
I don't expect anything else from unfolding a loop, but the sequential structure is so different from the deeply nested structure of |td|.

And then, something unexpected yet familiar appears in the translated diagram.

\noindent
\begin{minipage}{.45\textwidth}
\begin{code}
bu s e g 3 =  unTip ∘

                id          ∘

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
\[ \tikzfig{bu} \]
\end{minipage}

There are also two phases for table construction and demolition, and the demolition phase is \emph{exactly the same} as the one in |td|!

The string diagram is truly helpful this time.
Now I see that, as Richard hinted, I could rewrite the traditional expression using the naturality of |unTip| and |retabulate| to push |g|~and~|e| to the left of the sequence and separate the two phases.
But on the string diagram, all those rewritings amount to nothing more than gently pulling the two phases apart from each other (making the dashed line horizontal).
In fact I don't even want or bother to pull, because on this diagram I can already see both the sequence (the dots appearing one by one along the vertical direction) and the result of rewriting the sequence using naturality at the same time.

%\todo[inline]{Specialised cases (with a concrete size) only; production and consumption parts, which can be separated by naturality.}

So, modulo naturality, the two algorithms have the same table demolition phase but different table construction phases.
If I can prove that their table construction phases are equal, then (in addition to the parametricity-based proof) I will have another proof that the two algorithms are equal.
For |td|, the construction phase is a right-leaning tree on the diagram, whereas for |bu| it's a left-leaning tree.
Maybe what I need is an equation about |blanks| and |retabulate| that can help me rotate a tree\ldots?

\[ \text{\lstinline{cd (choose k xs)}} \equals \text{\lstinline{mapB (choose k) (choose (k+1) xs)}} \]

The equation flashes through my mind.
Of course it has to be this equation --- I used it as a specification for \lstinline{cd}, the Haskell predecessor of |retabulate|.
How else would I introduce |retabulate| into the picture?
But first let me update this to a dependently typed string diagram.

\[ \tikzfig{rotation} \qquad\text{if |n > k|} \]

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
BT-isProp : ({ys : Vec a k} → isProp (p ys)) → isProp (BT(C n k) p xs)
\end{code}
And then the |rotation| equation can be proved trivially by invoking |BT-isProp| twice.
\begin{code}
rotation :
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

Oh well, at least |rotation| helps to check that the proof idea works before I embark on the general proof that |td| equals |bu|.
Conceptually I’ve figured it all out:
Both algorithms have two phases modulo naturality; their table demolition phases are exactly the same, and their table construction phases are equal due to the |BT-isProp| reasoning.
But the general proof is still going to take some work:
If I want to stick to string diagrams, I’ll need to translate the algorithms to inductively defined diagrams.
Moreover, the |BT-isProp| reasoning is formally an induction (on the length of the input list), which needs to be worked out.
And actually, compared with a diagrammatic but unformalised proof, I prefer a full Agda formalisation.
That means I’ll need to spell out a lot of detail, including naturality rewriting.
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
More precisely, `using~|g| to fill in a nested table' means something like |mapBT (mapBT g) : BT(C 3 2) (BT(C 2 1) (BT(C 1 0) s)) xs → BT(C 3 2) (BT(C 2 1) s) xs|, where the result is at least two layers of tables, so there should be at least \emph{three} layers of tables for the solving of overlapping sub-problems to happen.
The bottom-up algorithm doesn't get to three layers of tables, and therefore avoids solving overlapping sub-problems.

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
