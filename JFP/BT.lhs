\documentclass{jfp}

\DeclareMathAlphabet{\mathsf}{OT1}{cmss}{m}{n}
\DeclareMathAlphabet{\mathsfb}{OT1}{cmss}{bx}{n}

\usepackage{mathtools}

\usepackage{xifthen}
\newcommand{\varcitet}[3][]{\citeauthor{#2}#3~\ifthenelse{\isempty{#1}}{\citeyearpar{#2}}{\citeyearpar[#1]{#2}}}

\setlength{\marginparwidth}{2.2cm}
\usepackage[obeyFinal,color=yellow,textsize=footnotesize]{todonotes}

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
%format idenR = "\Con{iden}"
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
%format comp = "\Var{comp}"
%format eq = "\Var{eq}"
%format eq' = "\Var{eq^\prime}"
%format f = "\Var f"
%format g = "\Var g"
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
%format t = "\Var t"
%format u = "\Var u"
%format x = "\Var x"
%format xs = "\Var{xs}"
%format ys = "\Var{ys}"
%format zs = "\Var{zs}"

\begin{document}

\setlength{\mathindent}{2\parindent}

\journaltitle{JFP}
\cpr{Cambridge University Press}
\doival{10.1017/xxxxx}

\totalpg{\pageref{lastpage01}}
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

\maketitle[F]

\section{Introduction}

\todo[inline]{Positioned as a follow-up to Shin's~\citeyearpar{Mu-sublists} paper, but kept (almost) independent until the comparison near the end (but maybe mention the methodological difference in the beginning); just quote and reuse Shin's problem introduction text?}

\section{The induction principle and its representations}

\todo[inline]{Aim for an induction principle from the beginning (naturally switching to type families); start with the functional/container~\citep{Altenkirch-indexed-containers} representation, but notice that \citet{Bird-zippy-tabulations} used an inductive data structure}

\todo[inline]{Directly follow Shin's definition of immediate sublist based on element \emph{dropping}; directly generalise to |DropR n| because we know we'll deal with all levels later}
\begin{code}
data DropR : ℕ → List A → List A → Set where
  idenR :                           DropR    zero    xs        xs
  dropR : DropR       n   xs ys  →  DropR (  suc n)  (x ∷ xs)  ys
  keepR : DropR (suc  n)  xs ys  →  DropR (  suc n)  (x ∷ xs)  (x ∷ ys)
\end{code}

\begin{code}
   {A : Set} (P : List A → Set)
→  (∀ {ys} → (∀ {zs} → DropR 1 ys zs → P zs) → P ys)
→  (xs : List A) → P xs
\end{code}

\todo[inline]{The `mother of all monads' construction \citep{Filinski-representing-monads}}

\begin{code}
drop : ℕ → List A → Nondet (List A)
drop    zero    xs        = return xs
drop (  suc n)  []        = mzero
drop (  suc n)  (x ∷ xs)  = mplus (drop n xs) (fmap (x ∷_) (drop (suc n) xs))
\end{code}

\begin{code}
record Monoid (M : Set ℓ) : Set ℓ where
  constructor monoid
  field
    _⊕_  : M → M → M
    ∅    : M
\end{code}
\todo{omit the laws, which could be included but are not needed}


\begin{code}
drop : ℕ → List A → ⦃ Monoid B ⦄ → (List A → B) → B
drop    zero    xs        k = k xs
drop (  suc n)  []        k = ∅
drop (  suc n)  (x ∷ xs)  k = drop n xs k {-"\kern1.5pt"-} ⊕ {-"\kern1.5pt"-} drop (suc n) xs (k ∘ (x ∷_))
\end{code}

\begin{code}
dropL : ℕ → List A → List (List A)
dropL n xs = drop n xs ⦃ monoid _++_ [] ⦄ (_∷ [])
\end{code}

\begin{code}
DropR n xs ys {-"\kern2pt"-} ≅ {-"\kern2pt"-} drop n xs ⦃ monoid _⊎_ ⊥ ⦄ (_≡ ys)
\end{code}

\begin{code}
Drop n P xs {-"\kern2pt"-} ≅ {-"\kern2pt"-} drop n xs ⦃ monoid _×_ ⊤ ⦄ P
\end{code}

\begin{code}
data Drop : ℕ → (List A → Set) → List A → Set where
  tip  :  P xs                                        →  Drop    zero    P xs
  nil  :                                                 Drop (  suc n)  P []
  bin  :  Drop n P xs → Drop (suc n) (P ∘ (x ∷_)) xs  →  Drop (  suc n)  P (x ∷ xs)
\end{code}

\begin{code}
ImmediateSublistInduction : Set₁
ImmediateSublistInduction  = {A : Set} (P : List A → Set)
                           → (∀ {ys} → Drop 1 P ys → P ys)
                           → (xs : List A) → P xs
\end{code}

\section{The top-down algorithm}

\begin{code}
td : ImmediateSublistInduction
td {A} P f xs = td' (length xs) xs refl
  where
    td' : (l : ℕ) (xs : List A) → length xs ≡ l → P xs
    td'    zero    [] eq = f nil
    td' (  suc l)  xs eq = f (map (td' l _) (subs l xs eq))
\end{code}

\begin{code}
subs  :   (l : ℕ) (xs : List A) → length xs ≡ suc l
      →'  Drop 1 (λ ys → length ys ≡ l) xs
\end{code}

\begin{code}
map : (∀ {ys} → P ys → Q ys) → ∀ {xs} → Drop n P xs → Drop n Q xs
\end{code}

\section{The bottom-up algorithm}

\begin{code}
bu : ImmediateSublistInduction
bu P f = bu' _ ∘ blank
  where
    bu' : (n : ℕ) → Drop n P xs → P xs
    bu'    zero    = unTip
    bu' (  suc n)  = bu' n ∘ map f ∘ upgrade
\end{code}

\begin{code}
blank : (xs : List A) → Drop (suc (length xs)) P xs
\end{code}

\begin{code}
unTip : Drop 0 P xs → P xs
unTip (tip p) = p
\end{code}

\begin{code}
upgrade : Drop (suc n) P xs → Drop n (Drop 1 P) xs
upgrade         nil                           = ground
upgrade t @  (  bin      (  tip _)    _    )  = tip t
upgrade      (  bin         nil       nil  )  = bin ground nil
upgrade      (  bin t @  (  bin _ _)  u    )  = bin  (upgrade t)
                                                     (zipWith (bin ∘ tip) t (upgrade u))
\end{code}

\begin{code}
ground : Drop n (Drop 1 P) []
ground {n =' zero   } = tip nil
ground {n =' suc _  } = nil
\end{code}

\section{Equality between the two algorithms}

\begin{code}
UnaryParametricity : ImmediateSublistInduction → Set₁
UnaryParametricity ind =
  {A : Set}  {P   : List A → Set}                 (Q  :   ∀ {ys} → P ys → Set) 
             {f   : ∀ {ys} → Drop 1 P ys → P ys}  (g  :   ∀ {ys} {ps : Drop 1 P ys}
                                                      →'  All Q ps → Q (f ps))
             {xs  : List A} → Q (ind P f xs)
\end{code}

\begin{code}
All : (∀ {ys} → P ys → Set) → Drop n P xs → Set
All Q (  tip p)    = Q p
All Q    nil       = ⊤
All Q (  bin t u)  = All Q t × All Q u
\end{code}

\todo[inline]{Parametricity replacing a set of computation rules in the uniqueness proof of an induction principle}

\begin{code}
ComputationRule : ImmediateSublistInduction → Set₁
ComputationRule ind =
  {A : Set} {P : List A → Set} {f : ∀ {ys} → Drop 1 P ys → P ys} {xs : List A}
  {ps : Drop 1 P xs} → All (λ {ys} p → ind P f ys ≡ p) ps → ind P f xs ≡ f ps
\end{code}

\begin{code}
uniqueness :
     (ind ind' : ImmediateSublistInduction)
  →  ComputationRule ind → UnaryParametricity ind'
  →  {A : Set} (P : List A → Set) (f : ∀ {ys} → Drop 1 P ys → P ys) (xs : List A)
  →  ind P f xs ≡ ind' P f xs
uniqueness ind ind' comp param' P f xs = param' (λ {ys} p → ind P f ys ≡ p) comp
\end{code}
\todo{\varcitet{Bernardy-proofs-for-free}{'s} translation or internal parametricity~\citep{Van-Muylder-internal-parametricity}}

\section{Discussion}

\todo[inline]{Detailed but informal comparison with Shin's development; theory still missing for formally relating Shin's equational proof and correctness by type checking}

\todo[inline]{Efficiency comparison between the inductive and container representations}

\section*{Acknowledgement}

\todo[inline]{Zhixuan Yang (mother of all monads, induction principles and parametricity), James McKinna (container representation)}

\bibliographystyle{jfplike}
\bibliography{../../bib/bib}

\end{document}