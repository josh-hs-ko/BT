\documentclass[fleqn]{jfp}

% Build using:
%  lhs2Tex --agda BT.lhs | pdflatex --jobname=BT

\DeclareMathAlphabet{\mathsf}{OT1}{cmss}{m}{n}
\DeclareMathAlphabet{\mathsfb}{OT1}{cmss}{bx}{n}

\usepackage{mathtools}

\crefformat{equation}{(#2#1#3)}

\usepackage{xifthen}
\newcommand{\varcitet}[3][]{{\protect\NoHyper\citeauthor{#2}\protect\endNoHyper}#3~\ifthenelse{\isempty{#1}}{\citeyearpar{#2}}{\citeyearpar[#1]{#2}}}

\setlength{\marginparwidth}{2.2cm}
\usepackage[obeyFinal,color=yellow,textsize=footnotesize]{todonotes}

\usepackage{lastpage}

\let\Bbbk\relax
%include agda.fmt

\DeclareUnicodeCharacter{2205}{\emptyset}
\DeclareUnicodeCharacter{2245}{\cong}
\DeclareUnicodeCharacter{2261}{\equiv}
\DeclareUnicodeCharacter{228E}{\uplus}
\DeclareUnicodeCharacter{2295}{\oplus}
\DeclareUnicodeCharacter{2983}{\{\kern-2.5pt\{\kern-1.5pt}
\DeclareUnicodeCharacter{2984}{\kern-1.5pt\}\kern-2.5pt\}}

\renewcommand{\Keyword}{\mathbf}
\renewcommand{\Varid}{\mathsf}
\renewcommand{\Conid}{\mathsf}

\renewcommand{\textrightarrow}{\mathrel\to}

\newcommand{\ignorenext}[1]{}

%format →' = "\kern-.345em\mathrlap{\to}"
%format =' = "\unskip=\ignorenext"
%format @ = "\unskip@\ignorenext"
%format Setω = Set "_{" ω "}"
%format _≡ = _ ≡
%format _⊎_ = _ ⊎ _
%format × = "{\times}"
%format _×_ = _ × _
%format ∘ = "\unskip\mathrel\circ\ignorenext"
%format _∷_ = _ "\kern.5pt" ∷ _
%format _∷ = _ ∷
%format ∷_ = ∷ _
%format ++ = + "\kern-3.5pt" +
%format _++_ = _ ++ _
%format _⊕_ = _ ⊕ _
%format DropR = Drop "^{" R "}"
%format dropL = drop "^{" L "}"

%format 0 = "\mathrm 0"
%format 1 = "\mathrm 1"

\newcommand{\Con}{\mathsfb}

%format zero = "\Con{zero}"
%format suc = "\Con{suc}"
%format returnR = "\Con{return}"
%format keepR = "\Con{keep}"
%format dropR = "\Con{drop}"
%format monoid = "\Con{monoid}"
%format tip = "\Con{tip}"
%format nil = "\Con{nil}"
%format bin = "\Con{bin}"
%format refl = "\Con{refl}"

\newcommand{\Var}{\mathit}

%format A = "\Var A"
%format B = "\Var B"
%format C = "\Var C"
%format comp = "\Var{comp}"
%format eq = "\Var{eq}"
%format eq' = "\Var{eq^\prime}"
%format f = "\Var f"
%format g = "\Var g"
%format h = "\Var h"
%format ind = "\Var{ind}"
%format ind' = "\Var{ind^\prime}"
%format k = "\Var k"
%format l = "\Var l"
%format M = "\Var M"
%format m = "\Var m"
%format n = "\Var n"
%format P = "\Var P"
%format p = "\Var p"
%format param' = "\Var{param^\prime}"
%format ps = "\Var{ps}"
%format Q = "\Var Q"
%format R = "\Var R"
%format t = "\Var t"
%format u = "\Var u"
%format x = "\Var x"
%format y = "\Var y"
%format xs = "\Var{xs}"
%format ys = "\Var{ys}"
%format zs = "\Var{zs}"

\begin{document}

\setlength{\mathindent}{2\parindent}

\journaltitle{JFP}
\cpr{Cambridge University Press}
\doival{10.1017/xxxxx}

\totalpg{\pageref{LastPage}}
\jnlDoiYr{2025}

\lefttitle{H.-S. Ko and S.-C. Mu}
\righttitle{Bottom-up computation using trees of sublists: A dependently typed approach}

\title{Bottom-up computation using trees of sublists:\\ A dependently typed approach}

\begin{authgrp}
\author{Hsiang-Shang Ko}
\affiliation{Institute of Information Science, Academia Sinica, Taipei, Taiwan\\(\email{joshko@@iis.sinica.edu.tw})}
\author{Shin-Cheng Mu}
\affiliation{Institute of Information Science, Academia Sinica, Taipei, Taiwan\\(\email{scm@@iis.sinica.edu.tw})}
\end{authgrp}

\begin{abstract}
We revisit the problem about a recursion scheme over immediate sublists studied by \citet{Mu-sublists}, and provide a dependently typed solution in Agda.
The recursion scheme can be implemented as either a top-down algorithm, which has a straightforward definition but results in lots of re-computation, or a bottom-up algorithm, which has a puzzling definition but avoids re-computation.
We show that the types can be made precise to guide and understand the developments of the algorithms.
In particular, the key data structure ---binomial trees--- used in the bottom-up algorithm can be derived from the problem specification.
The precise types also allow us to prove that the two algorithms are extensionally equal using parametricity.
Despite apparent dissimilarities, our parametricity-based proof turns out to be a more structured and economic version of \citeauthor{Mu-sublists}'s equational proof.
\end{abstract}

\maketitle[F]

\section{Introduction}
\label{sec:introduction}

Given a list |xs|, its \emph{immediate sublists} are those lists obtained by removing exactly one of its elements.
For example, the four immediate sublists of |"abcd"| are |"abc"|, |"abd"|, |"acd"|, and |"bcd"|.
\citet{Mu-sublists} considered the problem of computing a function~|h| such that |h xs| depends on values of~|h| at all the immediate sublists of |xs|.
More formally,
given |f : List B -> B|, compute |h : List A -> B| with such a top-down specification
\begin{equation}
|h xs = f (map h (subs xs))|
\label{eq:spec}
\end{equation}
where |subs : List A → List (List A)| computes immediate sublists.
Naively executing the specification results in lots of re-computation.
See \cref{fig:td-call-tree}, for example:
|h "ab"| is computed twice for |h "abc"| and |h "abd"|, and |h "ac"| twice for |h "abc"| and |h "acd"|.
%\todo{|h "a"| for both |h "ab"| and |h "ac"|? (then bumping into the problem of different base cases)}

The problem is derived from \varcitet{Bird-zippy-tabulations}{'s} study of the relationship between top-down and bottom-up algorithms.
A bottom-up strategy that avoids re-computation is shown in \cref{fig:sublists-lattice}.
Values of |h| on inputs of length~$n$ are stored in level~$n$ to be reused.
Each level $n+1$ is computed from level~$n$, until we reach the top.
It may appear that this bottom-up strategy can be implemented by representing each level using a list, but this turns out to be impossible.
%It will turn out that, however, computing the indices needed to fetch the corresponding entries is not pretty, and sometimes impossible without additional information.
%\todo{JK: seems simpler to just say a list-based implementation is impossible}
Instead, Bird represents each level using a tip-valued binary tree:%
\footnote{We use Agda in this paper, while both \citet{Bird-zippy-tabulations} and \citet{Mu-sublists} use Haskell; some of their definitions are quoted in this section but translated into Agda notation for consistency.}
\begin{spec}
data BT (A : Set) : Set where
  tip  : A            → BT A
  bin  : BT A → BT A  → BT A
\end{spec}
with functions |mapBT : (A → B) → BT A → BT B| and |zipBTWith : (A → B → C) →| |BT A →| |BT B →| |BT C|, respectively the mapping and zipping functions for |BT|, having expected definitions.
Let |t|~be a tree representing level $n$.
To compute level $n+1$, we need a function |upgrade : BT A → BT (List A)|, a natural transformation copying and rearranging elements in~|t|, such that |mapBT f (upgrade t)| represents level $n+1$.
Bird suggests the following definition of |upgrade|
(which is directly translated into Agda notation from Bird's Haskell program, and is not valid Agda --- we will fix it later):%
\footnote{The name |upgrade| is given by \citet{Mu-sublists}, while the same function is called |cd| by \citet{Bird-zippy-tabulations}.}
%\todo{SCM: Or, "the code below, adapted from Bird's, is not yet a total definition. We will fix it later." Which is preferred? JK: |let tip xs = ...| is also invalid, so let's just say the definition is not valid Agda\ldots}
\begin{spec}
upgrade : BT A → BT (List A)
upgrade (bin (tip x)  (tip y)  ) = tip (x ∷ y ∷ [])
upgrade (bin t        (tip y)  ) = bin (upgrade t) (mapBT (_∷ [ y ]) t)
upgrade (bin (tip x)  u        ) = let tip xs = upgrade u in tip (x ∷ xs)
upgrade (bin t        u        ) = bin (upgrade t) (zipBTWith _∷_ t (upgrade u))
\end{spec}

\begin{figure}[t]
\centering
\includegraphics[width=0.95\textwidth]{pics/td-call-tree.pdf}
\caption{Computing |h "abcd"| top-down.}
\label{fig:td-call-tree}
\end{figure}

\begin{figure}[t]
\centering
\includegraphics[width=0.75\textwidth]{pics/sublists-lattice.pdf}
\caption{Computing |h "abcd"| bottom-up.}
\label{fig:sublists-lattice}
\end{figure}

If you feel puzzled by |upgrade|, so were we.
Being the last example in the paper, Bird does not offer much explanation.
The function |upgrade| is as concise as it is cryptic.
The trees appear to obey some shape constraints --- Bird calls them \emph{binomial trees}, hence the name |BT|, but neither the constraints nor how |upgrade| maintains them is explicitly stated.

Fascinated by the definition, \citet{Mu-sublists} offers a specification of |upgrade| and a derivation, and then proves that the bottom-up algorithm is extensionally equal to the top-down specification/algorithm, all using traditional equational reasoning.
As an interlude, Mu also shows (in his Section~4.3) a dependently typed version of |upgrade|, which uses an indexed version of |BT| that encodes the shape constraint on binomial trees, although Mu does not explore the direction further.
In this paper, we go down the road not (thoroughly) taken and see how far it leads.
In a dependently typed setting, can we derive the binomial trees by formalising in their types what we intend to compute?
How effectively can the type information help us to implement the top-down and bottom-up algorithms correctly?
And does the type information help us to prove that the two algorithms are extensionally equal?
%Instead of going into the tedious details of |upgrade|,
%can we put enough information in type-level such that, by exploiting the fact the functions having the (more informative) type must be unique,\todo{Spoiler!}
%the equivalence of the top-down specification and the bottom-up algorithm automatically follows?

%\todo[inline]{Positioned as a follow-up to Shin's~\citeyearpar{Mu-sublists} paper, but kept (almost) independent until the comparison near the end (but maybe mention the methodological difference in the beginning); just quote and reuse Shin's problem introduction text?}

\section{The induction principle and its representations}
\label{sec:induction-principle}

First, notice that we are dealing with a \emph{recursion scheme}~\citep{Yang-recursion-schemes} of type
\begin{equation}
|(List B → B) → List A → B|
\label{eq:non-dependently-typed-recursion-scheme}
\end{equation}
In a dependently typed setting, recursion schemes become \emph{elimination} or \emph{induction principles}.
Instead of ending the type~\cref{eq:non-dependently-typed-recursion-scheme} with |List A → B|, we should aim for |(xs : List A) → P xs| and make it an induction principle, of which |P : List A → Set| is the motive~\citep{McBride-motive}.
Like all induction principles, the motive should be established and preserved in a way that follows the recursive structure of the computation: whenever |P|~holds for all the immediate sublists of a list |ys|, it should hold for |ys| as well.

To define the induction principle formally, first we need to define immediate sublists --- in fact we will just give a more general definition of sublists since we will need to refer to all of them during the course of the computation.
\citet{Bird-zippy-tabulations} and \citet{Mu-sublists} define an immediate sublist of |xs| as a list obtained by dropping one element from |xs|; more generally, a sublist can be obtained by dropping some number of elements.
Element dropping can be written as an inductively defined relation:
\begin{code}
data DropR : ℕ → List A → List A → Set where
  returnR  :                           DropR    zero    xs        xs
  dropR    : DropR       n   xs ys  →  DropR (  suc n)  (x ∷ xs)  ys
  keepR    : DropR (suc  n)  xs ys  →  DropR (  suc n)  (x ∷ xs)  (x ∷ ys)
\end{code}
Then we can write down the induction principle:
\begin{code}
{A : Set} (P : List A → Set)
(f : ∀ {ys} → (∀ {zs} → DropR 1 ys zs → P zs) → P ys)
(xs : List A) → P xs
\end{code}

Notice that the induction hypotheses are represented as a function of type
\begin{equation}\label{eq:container-ih}
|∀ {zs} → DropR 1 ys zs → P zs|
\end{equation}
making the type of the premise~|f| higher-order, whereas the type~\cref{eq:non-dependently-typed-recursion-scheme} uses a list, a first-order data structure.
Below we derive an indexed data type |Drop n P xs| that represents universal quantification over all the sublists obtained by dropping |n|~elements from |xs|; in particular, |Drop 1 P ys| will be equivalent to the function type~\cref{eq:container-ih}.

We start by (re)defining element dropping as a nondeterministic function:
\begin{code}
drop : ℕ → List A → Nondet (List A)
drop    zero    xs        = return xs
drop (  suc n)  []        = mzero
drop (  suc n)  (x ∷ xs)  = mplus (drop n xs) (fmap (x ∷_) (drop (suc n) xs))
\end{code}
|Nondet| is a (relative) monad~\citep{Altenkirch-relative-monads} equipped with a fail operation (|mzero : Nondet A|) and nondeterministic choice (|mplus : Nondet A → Nondet A → Nondet A|), and we choose the codensity representation~\citep{Filinski-representing-monads, Hinze-Kan-extensions}
\begin{code}
Nondet : Set → Setω
Nondet A = ∀ {ℓ} {M : Set ℓ} → ⦃ Monoid M ⦄ → (A → M) → M
\end{code}
where the result type~|M| should be a monoid, defined as usual:
\begin{code}
record Monoid (M : Set ℓ) : Set ℓ where
  constructor monoid
  field
    _⊕_  : M → M → M
    ∅    : M
\end{code}
(The monoid laws could be included but are not needed in our development.)
If we expand the definitions of |Nondet| and its operations in |drop|, we get
\begin{code}
drop : ℕ → List A → ⦃ Monoid M ⦄ → (List A → M) → M
drop    zero    xs        k = k xs
drop (  suc n)  []        k = ∅
drop (  suc n)  (x ∷ xs)  k = drop n xs k {-"\kern1.5pt"-} ⊕ {-"\kern1.5pt"-} drop (suc n) xs (k ∘ (x ∷_))
\end{code}
which we can specialise to various forms.
For example, we can specialise |drop| to compute all the sublists of a particular length using the list monad:
\begin{code}
dropL : ℕ → List A → List (List A)
dropL n xs = drop n xs ⦃ monoid _++_ [] ⦄ (_∷ [])
\end{code}

More interestingly, we can also specialise |drop| to compute types.
For example, |DropR| can alternatively be defined in continuation-passing style by
\begin{code}
DropR n xs ys {-"\kern2pt"-} ≅ {-"\kern2pt"-} drop n xs ⦃ monoid _⊎_ ⊥ ⦄ (_≡ ys)
\end{code}
which amounts to existential quantification over sublists.
To obtain universal quantification, we supply the dual monoid:
\begin{code}
Drop n P xs {-"\kern2pt"-} ≅ {-"\kern2pt"-} drop n xs ⦃ monoid _×_ ⊤ ⦄ P
\end{code}
Rewriting the function definition as a data type definition (by turning each clause into a constructor), we get
\begin{code}
data Drop : ℕ → (List A → Set) → List A → Set where
  tip  :  P xs                                        →  Drop    zero    P xs
  nil  :                                                 Drop (  suc n)  P []
  bin  :  Drop n P xs → Drop (suc n) (P ∘ (x ∷_)) xs  →  Drop (  suc n)  P (x ∷ xs)
\end{code}
which we will use to represent the induction hypotheses in the induction principle:
\begin{code}
ImmediateSublistInduction : Set₁
ImmediateSublistInduction =  {A : Set} (P : List A → Set)
                             (f : ∀ {ys} → Drop 1 P ys → P ys)
                             (xs : List A) → P xs
\end{code}
Note that |Drop| is an indexed version of |BT| (\cref{sec:introduction}) that has an additional |nil| constructor.
(We will see in \cref{sec:bu} why it is beneficial to include |nil|.)
Comparing the type~\cref{eq:non-dependently-typed-recursion-scheme} with |ImmediateSublistInduction|, a potentially drastic change is that the list of induction hypotheses is replaced with a tree of type |Drop 1 P ys| here.
However, such a tree is actually list-shaped (constructed using |nil| and |bin ∘ tip|), so |ImmediateSublistInduction| is really just a more informative version of the type~\cref{eq:non-dependently-typed-recursion-scheme}.

In the subsequent \cref{sec:td,sec:bu} we will implement the top-down and bottom-up algorithms as programs of type |ImmediateSublistInduction|.
These are fairly standard exercises in dependently typed programming (except perhaps for the |upgrade| function used in the bottom-up algorithm), and our implementations are by no means the only solutions.%
\footnote{Even the induction principle has alternative formulations, one of which is explored by \citet{Ko-BT}.}
The reader may want to try the exercises for themself, and is not obliged to go through the detail of our programs.
We will prove that the two algorithms are extensionally equal in \cref{sec:equality}, to understand which it will not be necessary to know how the two algorithms are implemented.

\section{The top-down algorithm}
\label{sec:td}

The specification~\cref{eq:spec} is essentially an executable definition of the top-down algorithm.
This definition would not pass Agda's termination check though, because the immediate sublists in |subs xs| would not be recognised as structurally smaller than |xs|.
One way to make termination evident is to make the length of |xs| explicit and perform induction on the length.
The following function |td| does this by invoking |td'|, which takes as additional arguments a natural number~|l| and an equality proof stating that the length of |xs| is~|l|.
The function |td'| then performs induction on~|l| and does the real work.
\begin{code}
td : ImmediateSublistInduction
td {A} P f xs = td' (length xs) xs refl
  where
    td' : (l : ℕ) (xs : List A) → length xs ≡ l → P xs
    td'    zero    [] eq = f nil
    td' (  suc l)  xs eq = f (map (λ {ys} → td' l ys) (subs l xs eq))
\end{code}
In the first case of |td'|, where |xs| is~|[]|, the final result is simply |f nil : P []|.
In the second case of |td'|, where the length of |xs| is |suc l|, the function |subs| is adapted to construct equality proofs that all the immediate sublists of |xs| have length~|l|.
\begin{code}
subs : (l : ℕ) (xs : List A) → length xs ≡ suc l → Drop 1 (λ ys → length ys ≡ l) xs
\end{code}
With these equality proofs, we can then invoke |td'| inductively on every immediate sublist of |xs| with the help of the |map| function for |Drop|,
\begin{code}
map : (∀ {ys} → P ys → Q ys) → Drop n P xs → Drop n Q xs
\end{code}
and again use~|f| to compute the final result.

\section{The bottom-up algorithm}
\label{sec:bu}

Given an input list |xs|, the bottom-up algorithm |bu| first creates a tree representing `level~$-1$' below the lattice in \cref{fig:sublists-lattice}.
This `underground' level contains results for those sublists obtained by removing |suc (length xs)| elements from |xs|; there are no such sublists, so the tree contains no elements, although the tree itself still exists (representing a proof of a vacuous universal quantification):
\begin{code}
base : (xs : List A) → Drop (suc (length xs)) P xs
\end{code}
The algorithm then enters a loop |bu'| and constructs each level of the lattice from bottom up, that is, a tree of type |Drop n P xs| for each~|n|, with |n|~decreasing:
\begin{code}
bu : ImmediateSublistInduction
bu P f = bu' _ ∘ base
  where
    bu' : (n : ℕ) → Drop n P xs → P xs
    bu'    zero    = unTip
    bu' (  suc n)  = bu' n ∘ map f ∘ upgrade
\end{code}
When the loop counter reaches |zero|, the tree contains exactly the result for |xs|, which we can extract using
\begin{code}
unTip : Drop zero P xs → P xs
unTip (tip p) = p
\end{code}
If the loop counter is |suc n|, we create a new tree of type |Drop n P xs| that is one level higher than the current tree of type |Drop (suc n) P xs|.
The type of this new tree says that it should contain results of type |P ys| for all the sublists |ys| at the higher level.
The |upgrade| function does half of the work by copying and rearranging the elements of the current tree to construct an intermediate tree representing the higher level:
\begin{code}
upgrade : Drop (suc n) P xs → Drop n (Drop 1 P) xs
\end{code}
It assembles for each~|ys| the induction hypotheses needed for computing |P ys| using~|f| --- that is, each element of the intermediate tree is a tree of type |Drop 1 P ys|.
Then |map f| does the rest of the work and produces the desired new tree of type |Drop n P xs|, and we enter the next iteration.

%\todo[inline]{SCM: now that |upgrade| was given in Section 1, we can add some words here briefly comparing them and showing that this one is adapted from the earlier one, while also saying that its actual definition does not matter? JK: Actually this may help to elide some explanation\ldots}

To implement |upgrade|, just follow the types, and most of the program writes itself.
\begin{code}
upgrade : Drop (suc n) P xs → Drop n (Drop 1 P) xs
upgrade         nil                           = underground
upgrade t @  (  bin      (  tip _)    _    )  = tip t
upgrade      (  bin         nil       nil  )  = bin underground nil
upgrade      (  bin t @  (  bin _ _)  u    )  = bin  (upgrade t)
                                                     (zipWith (bin ∘ tip) t (upgrade u))
\end{code}
where
\begin{code}
underground : Drop n (Drop 1 P) []
underground {n =' zero   } = tip nil
underground {n =' suc _  } = nil
\end{code}
and |zipWith| has the usual definition:
\begin{code}
zipWith  :   (∀ {ys} → P ys → Q ys → R ys)
         →'  Drop n P xs → Drop n Q xs → Drop n R xs
\end{code}
The last clause is the most difficult one to conceive, but can be copied exactly from the last clause of Bird's original program~(\cref{sec:introduction}) except that the list cons is replaced by the cons function |bin ∘ tip| for |Drop 1|--trees, which, as mentioned in \cref{sec:induction-principle}, are list-shaped.
It is a fruitful exercise to trace the constraints assumed and established throughout the construction described by the clause, now manifested as type information --- see \varcitet{Ko-BT}{'s} Section~2.3 for a solution (where |upgrade| is named |retabulate|).
%\citeauthor{Ko-BT} also explain how the second clause of |upgrade| subsumes the first and the third clauses of the original program.

The first and third clauses of |upgrade| involve |nil|, and are not in Bird's original program.
|Drop| trees containing |nil| correspond to empty levels below the lattice in \cref{fig:sublists-lattice} (which result from dropping too many elements from the input list).
\citet{Mu-sublists} avoids dealing with such empty levels by imposing conditions throughout his development --- for example, see \citeauthor{Mu-sublists}'s Section~4.3 for a version of |upgrade| (which is abbreviated as |up| there) with conditions.
We avoid those somewhat tedious conditions by including |nil| in |Drop| to represent the empty levels, and in exchange need to deal with these levels, which are easy to deal with though.

\section{Extensional equality between the two algorithms}
\label{sec:equality}

Now we have two different implementations of |ImmediateSublistInduction|, namely |td| and |bu|.
How do we prove that they compute the same results?

Actually, is it possible to write programs of type |ImmediateSublistInduction| to compute different results in Agda?
Since |ImmediateSublistInduction| is parametric in~|P|, intuitively a program of this type can only compute a result of type |P xs| using~|f|, and moreover, the index |xs| determines how |f|~needs to be applied to arrive at that result (to compute which |f|~needs to be applied to sub-results of type |P ys| for all the immediate sublists |ys| of |xs|, and all the sub-results can only be computed using~|f|, and so on).
So |td| and |bu| have to compute the same results simply because they have the same ---and special--- type!

To prove this formally, we use parametricity.
The following is the unary parametricity statement of |ImmediateSublistInduction| with respect to~|P| (whereas |A|~is treated merely as a fixed parameter), derived using \varcitet{Bernardy-proofs-for-free}{'s} translation:
\begin{code}
UnaryParametricity : ImmediateSublistInduction → Set₁
UnaryParametricity ind =
  {A : Set}  {P   : List A → Set}                 (Q  :   ∀ {ys} → P ys → Set)
             {f   : ∀ {ys} → Drop 1 P ys → P ys}  (g  :   ∀ {ys} {ps : Drop 1 P ys}
                                                      →'  All Q ps → Q (f ps))
             {xs  : List A} → Q (ind P f xs)
\end{code}
Unary parametricity can be understood in terms of invariant preservation: state an invariant~|Q| on values of type of the form |P ys|, provide a proof~|g| that |Q|~is preserved by~|f|, and then the results computed by |ind P f| will satisfy~|Q|.
In the type of~|g|, we need an auxiliary definition to formulate the premise that |Q|~is satisfied by all the elements in a |Drop| tree:
\begin{code}
All : (∀ {ys} → P ys → Set) → Drop n P xs → Set
All Q (  tip p)    = Q p
All Q    nil       = ⊤
All Q (  bin t u)  = All Q t × All Q u
\end{code}

Now the equality between |td| and |bu| is fairly straightforward to prove: first we derive a proof of |UnaryParametricity bu| (for example using \citeauthor{Bernardy-proofs-for-free}'s translation again); then, given |P|~and~|f|, we invoke the parametricity proof with the invariant |λ {ys} p → td P f ys ≡ p| saying that any |p : P ys| can only be the result computed by |td P f ys| (corresponding to our intuition above); finally, we can construct the remaining argument~|g| and arrive at a proof of |{xs : List A} → td P f xs ≡ bu P f xs|.

If we look at the argument~|g| in more detail, we will see that we can refactor the proof to gain a bit more structure and generality.
The instantiated type of~|g| is
\begin{code}
∀ {ys} {ps : Drop 1 P ys} → All (λ {zs} p → td P f zs ≡ p) ps → td P f ys ≡ f ps
\end{code}
This says that computing |td P f ys| is the same as applying~|f| to |ps| where every~|p| in |ps| is already a result computed by |td P f| --- this has the same computational content as the specification~\cref{eq:spec}, and is a formulation of the \emph{computation rule} of |ImmediateSublistInduction|, satisfied by |td|!
%That is, computation rules can be formulated as a form of invariant preservation.
Therefore we can formulate the computation rule for any implementation |ind| of |ImmediateSublistInduction|,
\begin{code}
ComputationRule : ImmediateSublistInduction → Set₁
ComputationRule ind =
  {A : Set} {P : List A → Set} {f : ∀ {ys} → Drop 1 P ys → P ys} {xs : List A}
  {ps : Drop 1 P xs} → All (λ {ys} p → ind P f ys ≡ p) ps → ind P f xs ≡ f ps
\end{code}
restate and prove the equality as a slightly more general theorem,
\begin{code}
uniqueness :
     (ind ind' : ImmediateSublistInduction)
  →  ComputationRule ind → UnaryParametricity ind'
  →  {A : Set} (P : List A → Set) (f : ∀ {ys} → Drop 1 P ys → P ys) (xs : List A)
  →  ind P f xs ≡ ind' P f xs
uniqueness ind ind' comp param' P f xs = param' (λ {ys} p → ind P f ys ≡ p) comp
\end{code}
and finally instantiate the theorem for |td| and |bu| by discharging the proof obligations |ComputationRule td| and |UnaryParametricity bu|.
(Our |td| in \cref{sec:td} does not satisfy the computation rule definitionally because it performs a different form of induction on the length of the input list, to make termination evident to Agda.
A proof of |ComputationRule td| is therefore not immediate, but only takes a small amount of work.)

\section{Methodological comparisons}

Usually, we prove two implementations |ind| and |ind'| of an induction principle to be equal assuming that both |ind| and |ind'| satisfy the set of computation rules coming with the induction principle.
For example, for |ImmediateSublistInduction| we can prove
\begin{code}
   (ind ind' : ImmediateSublistInduction)
→  ComputationRule ind → ComputationRule ind'
→  {A : Set} (P : List A → Set) (f : ∀ {ys} → Drop 1 P ys → P ys) (xs : List A)
→  ind P f xs ≡ ind' P f xs
\end{code}
The |uniqueness| theorem in \cref{sec:equality} demonstrates (in terms of |ImmediateSublistInduction|) that we can alternatively assume that one implementation, say |ind'|, satisfies unary parametricity instead, and we will still have a proof.
This is useful when |ind| can be easily proved to satisfy the set of computation rules whereas |ind'| cannot.
In this case, a parametricity proof for |ind'| is always mechanical ---if not automatic--- to derive, for example using \varcitet{Bernardy-proofs-for-free}{'s} translation or internal parametricity~\citep{Van-Muylder-internal-parametricity}, and we get to avoid a potentially difficult proof that |ind'| satisfies the set of computation rules.
This trick may be useful for porting recursion schemes or inventing efficient implementations of induction principles in a dependently typed setting.

\todo[inline]{Detailed but informal comparison with Shin's development: the dependently typed |upgrade| may look simpler but implicitly requires an extra argument during computation; (similarly) the base case of the induction principle starts from |[]| rather than singleton lists; contextual information is now at type level (cf \texttt{choose} in the derivation of \texttt{upgrade} and \texttt{td} in the equality proof)}

%\todo[inline]{Efficiency comparison between the inductive and functional/container~\citep{Altenkirch-indexed-containers} representations}

\citet{Mu-sublists} takes pains to prove that |td = bu|, while in this pearl the equivalence seems to follow almost for free from parametricity.
The trick is that the necessary properties are either enforced by types or established by parametricity.
The main property \citeauthor{Mu-sublists} needed is%
\footnote{Shown here are simple-typed version of the functions, used in \citet{Mu-sublists}, with some names changed to the counterparts in this pearl.
The types of these functions are:
|base : List A -> BT B|, |upgrade : BT b -> BT (List b)|,
|drop : Nat -> List a -> BT (List a)|,
|f : List B -> B|, |td : List A -> B|, and
|subs : List a -> List (List a)|.
}
\todo{I think it's better reusing the names in this paper, so the readers can quickly get an idea what these components are about (rather than having to learn a new name, say |ch| and remember that is a counterpart of |drop|).
The text explains the roles of each component, which I hope can be understood while keeping the types vague. If the readers needs to know the type, they can refer to the footnote.}
%format (repeat f (k)) = "{" f "}^{" k "}"
\begin{equation}
  |(repeat (mapBT f . upgrade) k) (base xs) = mapBT td (drop (suc n - k) xs)|
  \label{eq:muLemma1}
\end{equation}
That is an old-school way of saying that |bu| maintains an invariant.
Rather than enforcing shapes by types, the function |drop k xs| builds a tree of simple type |BT| whose shape is the same as our |Drop n P xs|.
The lefthand side of \eqref{eq:muLemma1} is the value computed after |k| iterations in |bu|:
|xs| is the initial input (having length |n|), |base| prepares an initial tree, on which |mapBT f . upgrade|, the body of |bu|, is performed |k| times.
The invariant is that the value must equal the righthand side:
a tree having shape |Drop (suc n - k) P xs|, whose values on tips are |td| applied to all those sublists of |xs| having |k| elements.
In contrast, in this pearl the shape of the trees are enforced by the type |Drop|,
while the invariant that the trees contain values of |td| is established using parametricity of |bu| by letting |Q {ys} p = td P f ys ≡ p|.

\citeauthor{Mu-sublists} proved \eqref{eq:muLemma1} by induction on |k|, which  coincides with the structure of |bu|.
While |UnaryParametricity| could in principle be proved mechanically once-for-all for all functions having the right type, if one had to prove |UnaryParametricity bu|, the proof would also follow the structure of |bu|.
Therefore it is essentially the proof of \eqref{eq:muLemma1} generalized to all invariants.
To prove \eqref{eq:muLemma1}, \citeauthor{Mu-sublists} relies on a property of |upgrade|, the proof of which being the main challenge in \cite{Mu-sublists}:
\begin{equation*}
   |upgrade (drop (suc k) xs) = mapBT subs (drop k xs)| \label{eq:muUpgrade}
\end{equation*}
That is, given a tree having shape |Drop (suc k) P xs|, |upgrade| computes a tree having shape |Drop k _ xs|, with the elements being the immediate sublists of |xs| --- which is exactly what the type of |upgrade| in this pearl says.

\section*{Acknowledgements}

Zhixuan Yang engaged in several discussions about induction principles, computation rules, and parametricity, leading to the current presentation of the parametricity-based proof; he also pointed out how |Nondet| is an instance of the codensity representation except that a dinaturality condition is omitted~\citep{Hinze-Kan-extensions}.
At the IFIP WG~2.1 meeting in April 2024, James McKinna suggested implementing |upgrade| on the higher-order representation~\cref{eq:container-ih} instead.
This definition of |upgrade| is extremely simple, but does not copy and reuse results on sublists, and therefore does not help to avoid re-computation.
However, this perspective does make the relationship between binomial trees and proofs of universal quantification clear, and leads to the inclusion of the |nil| constructor in |Drop| (which helps to simplify our definition of |upgrade|).
At the same meeting, Wouter Swierstra asked whether lists could be used instead of vectors in a previous definition of binomial trees~\citep{Ko-BT}.
There the definition of immediate sublists depends on the length of the input list, so it is more convenient to use vectors.
However, this question leads us to consider a definition of immediate sublists that does not depend on list length, and ultimately to the simpler definition of |Drop| (which uses lists instead of vectors).
We would like to thank all of them.

\bibliographystyle{jfplike}
\bibliography{../../bib/bib}

\end{document}
