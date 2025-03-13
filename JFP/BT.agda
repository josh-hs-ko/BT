-- Checked with Agda 2.7.0.1 and Standard Library 2.2

{-# OPTIONS --safe --with-K --large-indices --no-forced-argument-recursion #-}

open import Level using (Level; Setω)
open import Function using (_∘_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; pred; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; m≤n⇒m≤1+n)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Char using (Char)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; module ≡-Reasoning)

variable
  ℓ       : Level
  A B     : Set
  P P′ P″ : A → Set
  n       : ℕ
  x       : A
  xs ys   : List A

--------
-- Section 2

module ContainerRepresentation where

  data DropR : ℕ → List A → List A → Set where
    idenR :                       DropR  zero   xs       xs
    dropR : DropR      n  xs ys → DropR (suc n) (x ∷ xs) ys
    keepR : DropR (suc n) xs ys → DropR (suc n) (x ∷ xs) (x ∷ ys)

  ImmediateSublistInduction : Set₁
  ImmediateSublistInduction = {A : Set} (P : List A → Set)
                            → (∀ {ys} → (∀ {zs} → DropR 1 ys zs → P zs) → P ys)
                            → (xs : List A) → P xs

module MotherOfAllMonads where

  record Monoid (M : Set ℓ) : Set ℓ where
    constructor monoid
    field
      _⊕_ : M → M → M
      ∅   : M

  open Monoid ⦃ ... ⦄

  Nondet : Set → Setω
  Nondet A = ∀ {ℓ} {R : Set ℓ} → ⦃ Monoid R ⦄ → (A → R) → R

  return : A → Nondet A
  return x k = k x

  _>>=_ : Nondet A → (A → Nondet B) → Nondet B
  (mx >>= f) k = mx (λ x → f x k)

  fmap : (A → B) → Nondet A → Nondet B
  fmap f mx = mx >>= λ x → return (f x)

  mzero : Nondet A
  mzero k = ∅

  mplus : Nondet A → Nondet A → Nondet A
  mplus mx my k = mx k ⊕ my k

  drop : ℕ → List A → Nondet (List A)
  drop  zero   xs       = return xs
  drop (suc n) []       = mzero
  drop (suc n) (x ∷ xs) = mplus (drop n xs) (fmap (x ∷_) (drop (suc n) xs))

  -- drop : ℕ → List A → ∀ {ℓ} {R : Set ℓ} → ⦃ Monoid R ⦄ → (List A → R) → R
  -- drop  zero   xs       k = k xs
  -- drop (suc n) []       k = ∅
  -- drop (suc n) (x ∷ xs) k = drop n xs k ⊕ drop (suc n) xs (k ∘ (x ∷_))

  dropF : ℕ → List A → List (List A)
  dropF n xs = drop n xs ⦃ monoid _++_ [] ⦄ (_∷ [])

  test-dropF : dropF 2 ('a' ∷ 'b' ∷ 'c' ∷ 'd' ∷ [])
             ≡ ('c' ∷ 'd' ∷ []) ∷ ('b' ∷ 'd' ∷ []) ∷ ('b' ∷ 'c' ∷ []) ∷
               ('a' ∷ 'd' ∷ []) ∷ ('a' ∷ 'c' ∷ []) ∷ ('a' ∷ 'b' ∷ []) ∷ []
  test-dropF = refl

  DropR : ℕ → List A → List A → Set
  DropR n xs ys = drop n xs ⦃ monoid _⊎_ ⊥ ⦄ (ys ≡_)

  testDropR : DropR 2 ('a' ∷ 'b' ∷ 'c' ∷ 'd' ∷ []) ('b' ∷ 'c' ∷ [])
  testDropR = inj₁ (inj₂ (inj₂ (inj₁ refl)))

  Drop : ℕ → (List A → Set) → List A → Set
  Drop n P xs = drop n xs ⦃ monoid _×_ ⊤ ⦄ P

  testDrop : Drop 2 P ('a' ∷ 'b' ∷ 'c' ∷ 'd' ∷ [])
          → P ('c' ∷ 'd' ∷ []) × P ('b' ∷ 'd' ∷ []) × P ('b' ∷ 'c' ∷ [])
          × P ('a' ∷ 'd' ∷ []) × P ('a' ∷ 'c' ∷ []) × P ('a' ∷ 'b' ∷ [])
  testDrop ((x₀ , x₁ , x₂ , tt) , (x₃ , x₄ , tt) , (x₅ , tt) , tt , tt) =
    x₀ , x₁ , x₂ , x₃ , x₄ , x₅

data Drop : ℕ → (List A → Set) → List A → Set where
  tip : P xs                                       → Drop  zero   P xs
  nil :                                              Drop (suc n) P []
  bin : Drop n P xs → Drop (suc n) (P ∘ (x ∷_)) xs → Drop (suc n) P (x ∷ xs)

ImmediateSublistInduction : Set₁
ImmediateSublistInduction = {A : Set} (P : List A → Set)
                          → (∀ {ys} → Drop 1 P ys → P ys)
                          → (xs : List A) → P xs

--------
-- Section 3

map : (∀ {ys} → P ys → P′ ys) → ∀ {xs} → Drop n P xs → Drop n P′ xs
map f (tip p)   = tip (f p)
map f  nil      = nil
map f (bin t u) = bin (map f t) (map f u)

subs : (l : ℕ) (xs : List A) → length xs ≡ suc l → Drop 1 (λ ys → length ys ≡ l) xs
subs  zero   (_ ∷ []) eq = bin (tip refl) nil
subs (suc l) (_ ∷ xs) eq = let eq' = cong pred eq
                           in  bin (tip eq') (map (cong suc) (subs l xs eq'))

module Compact-td where

  td : ImmediateSublistInduction
  td {A} P f xs = td' (length xs) xs refl
    where
      td' : (l : ℕ) (xs : List A) → length xs ≡ l → P xs
      td'  zero   [] eq = f nil
      td' (suc l) xs eq = f (map (td' l _) (subs l xs eq))

td' : (∀ {ys} → Drop 1 P ys → P ys)
    → (l : ℕ) (xs : List A) → length xs ≡ l → P xs
td' f  zero   [] eq = f nil
td' f (suc l) xs eq = f (map (td' f l _) (subs l xs eq))

td : ImmediateSublistInduction
td {A} P f xs = td' f (length xs) xs refl

--------
-- Section 4

zipWith : (∀ {ys} → P ys → P′ ys → P″ ys)
        →  ∀ {xs} → Drop n P xs → Drop n P′ xs → Drop n P″ xs
zipWith f (tip p)    (tip q)    = tip (f p q)
zipWith f  nil        nil       = nil
zipWith f (bin t t') (bin u u') = bin (zipWith f t u) (zipWith f t' u')

underground : Drop n (Drop 1 P) []
underground {n = zero } = tip nil
underground {n = suc _} = nil

upgrade : Drop (suc n) P xs → Drop n (Drop 1 P) xs
upgrade    nil                = underground
upgrade t@(bin   (tip _)   _) = tip t
upgrade   (bin    nil    nil) = bin underground nil
upgrade   (bin t@(bin _ _) u) = bin (upgrade t)
                                    (zipWith (bin ∘ tip) t (upgrade u))

basement' : (xs : List A) {r : ℕ} → length xs ≤ r → Drop (suc r) P xs
basement' []       _       = nil
basement' (x ∷ xs) (s≤s l) = bin (basement' xs l) (basement' xs (m≤n⇒m≤1+n l))

basement : (xs : List A) → Drop (suc (length xs)) P xs
basement xs = basement' xs ≤-refl

unTip : Drop 0 P xs → P xs
unTip (tip p) = p

module Compact-bu where

  bu : ImmediateSublistInduction
  bu P f = bu' _ ∘ basement
    where
      bu' : (n : ℕ) → Drop n P xs → P xs
      bu'  zero   = unTip
      bu' (suc n) = bu' n ∘ map f ∘ upgrade

bu' : (∀ {ys} → Drop 1 P ys → P ys)
    → (n : ℕ) → Drop n P xs → P xs
bu' f  zero   = unTip
bu' f (suc n) = bu' f n ∘ map f ∘ upgrade

bu : ImmediateSublistInduction
bu P f = bu' f _ ∘ basement

--------
-- Section 5

All : (∀ {ys} → P ys → Set) → Drop n P xs → Set
All Q (tip p)   = Q p
All Q  nil      = ⊤
All Q (bin t u) = All Q t × All Q u

UnaryParametricity : ImmediateSublistInduction → Set₁
UnaryParametricity ind =
  {A : Set} {P : List A → Set}                (Q : ∀ {ys} → P ys → Set)
          → {f : ∀ {ys} → Drop 1 P ys → P ys} (g : ∀ {ys} {ps : Drop 1 P ys}
                                                 → All Q ps → Q (f ps))
          → {xs : List A} → Q (ind P f xs)

ComputationRule : (ind : ImmediateSublistInduction) → Set₁
ComputationRule ind =
  {A : Set} {P : List A → Set} {f : ∀ {ys} → Drop 1 P ys → P ys} {xs : List A}
  {t : Drop 1 P xs} → All (λ {ys} → ind P f ys ≡_) t → ind P f xs ≡ f t

revcat : List A → List A → List A
revcat []       ys = ys
revcat (x ∷ xs) ys = revcat xs (x ∷ ys)

module StandardUniqueness where

  uniqueness-lemma :
      (P : List A → Set) (f g : (xs : List A) → P xs) (zs : List A)
    → Drop 1 (λ ys → f (revcat zs ys) ≡ g (revcat zs ys)) xs
    → Σ[ t ∈ Drop 1 (P ∘ revcat zs) xs ] All (λ {ys} → f (revcat zs ys) ≡_) t
                                       × All (λ {ys} → g (revcat zs ys) ≡_) t
  uniqueness-lemma P f g zs  nil             = nil , tt , tt
  uniqueness-lemma P f g zs (bin (tip eq) u) =
    let (u' , all-f , all-g) = uniqueness-lemma P f g (_ ∷ zs) u
    in  bin (tip (g (revcat zs _))) u' , (eq , all-f) , (refl , all-g)

  uniqueness :
      (ind ind' : ImmediateSublistInduction)
    → ComputationRule ind → ComputationRule ind'
    → {A : Set} (P : List A → Set) (f : ∀ {ys} → Drop 1 P ys → P ys) (xs : List A)
    → ind P f xs ≡ ind' P f xs
  uniqueness ind ind' comp comp' P f =
    ind (λ xs → ind P f xs ≡ ind' P f xs)
        (λ {ys} ih →
        let (t , all , all') = uniqueness-lemma P (ind P f) (ind' P f) [] ih
        in  begin
              ind P f ys
                ≡⟨ comp all ⟩
              f t
                ≡⟨ comp' all' ⟨
              ind' P f ys
            ∎)
    where open ≡-Reasoning

uniqueness : (ind ind' : ImmediateSublistInduction)
           → ComputationRule ind → UnaryParametricity ind'
           → {A : Set} (P : List A → Set) (f : ∀ {ys} → Drop 1 P ys → P ys)
           → (xs : List A) → ind P f xs ≡ ind' P f xs
uniqueness ind ind' comp param' P f xs = param' (λ {ys} p → ind P f ys ≡ p) comp

-- td satisfies the computation rule

td'-computation :
    {A : Set} {P : List A → Set} {f : ∀ {ys} → Drop 1 P ys → P ys} {l : ℕ} {xs : List A}
  → (zs : List A) → length (revcat zs xs) ≡ suc l
  → (t : Drop 1 (P ∘ revcat zs) xs) → All (λ {ys} p → td P f (revcat zs ys) ≡ p) t
  → (eqs : Drop 1 (λ ys → length (revcat zs ys) ≡ l) xs)
  → map (td' f l _) eqs ≡ t
td'-computation zs eq  nil             _             nil                 = refl
td'-computation zs eq (bin (tip ._) u) (refl , all) (bin (tip refl) eqs) =
  cong₂ (bin ∘ tip) refl (td'-computation (_ ∷ zs) eq u all eqs)

td-computation' :
    {A : Set} {P : List A → Set} {f : ∀ {ys} → Drop 1 P ys → P ys}
    (l : ℕ) (xs : List A) (eq : length xs ≡ l) (t : Drop 1 P xs)
  → All (λ {ys} p → td P f ys ≡ p) t → td' f l xs eq ≡ f t
td-computation'  zero   [] refl nil _   = refl
td-computation' (suc l) xs eq   t   all = cong _ (td'-computation [] eq t all (subs l xs eq))

td-computation : ComputationRule td
td-computation {t = t} = td-computation' _ _ refl t

-- bu satisfies unary parametricity

unTipᴾ : (Q : ∀ {ys} → P ys → Set) (t : Drop 0 P xs) → All Q t → Q (unTip t)
unTipᴾ Q (tip p) q = q

mapᴾ : (Q : ∀ {ys} → P ys → Set) (Q′ : ∀ {ys} → P′ ys → Set)
       (f : ∀ {ys} → P ys → P′ ys) → (∀ {ys} {p : P ys} → Q p → Q′ (f p))
     → (t : Drop n P xs) → All Q t → All Q′ (map f t)
mapᴾ Q Q′ f fᴾ (tip p)   q         = fᴾ q
mapᴾ Q Q′ f fᴾ  nil      _         = tt
mapᴾ Q Q′ f fᴾ (bin t u) (tᴾ , uᴾ) = mapᴾ Q Q′ f fᴾ t tᴾ , mapᴾ Q Q′ f fᴾ u uᴾ

undergroundᴾ : (Q : ∀ {ys} → P ys → Set) (n : ℕ) → All (All (λ {ys} → Q {ys})) (underground {n})
undergroundᴾ Q  zero   = tt
undergroundᴾ Q (suc _) = tt

zipWithᴾ : (Q : ∀ {ys} → P ys → Set) (Q′ : ∀ {ys} → P′ ys → Set) (Q″ : ∀ {ys} → P″ ys → Set)
           (f : ∀ {ys} → P ys → P′ ys → P″ ys) → (∀ {ys} {p : P ys} {p′ : P′ ys} → Q p → Q′ p′ → Q″ (f p p′))
         → ∀ {xs} → (t : Drop n P xs) → All Q t → (u : Drop n P′ xs) → All Q′ u → All Q″ (zipWith f t u)
zipWithᴾ Q Q′ Q″ f fᴾ (tip p)    q          (tip p')   q'         = fᴾ q q'
zipWithᴾ Q Q′ Q″ f fᴾ  nil       _           nil       _          = tt
zipWithᴾ Q Q′ Q″ f fᴾ (bin t t') (tᴾ , t'ᴾ) (bin u u') (uᴾ , u'ᴾ) = zipWithᴾ Q Q′ Q″ f fᴾ t  tᴾ  u  uᴾ ,
                                                                    zipWithᴾ Q Q′ Q″ f fᴾ t' t'ᴾ u' u'ᴾ

upgradeᴾ : (Q : ∀ {ys} → P ys → Set) (t : Drop (suc n) P xs) → All Q t → All (All Q) (upgrade t)
upgradeᴾ {n = n}     Q    nil                 tᴾ       = undergroundᴾ Q n
upgradeᴾ             Q t@(bin   (tip _)   u)  tᴾ       = tᴾ
upgradeᴾ {n = suc n} Q   (bin    nil    nil)  tᴾ       = undergroundᴾ Q n , tt
upgradeᴾ             Q   (bin t@(bin _ _) u) (tᴾ , uᴾ) =
  upgradeᴾ Q t tᴾ , zipWithᴾ Q (All Q) (All (λ {ys} → Q {ys})) (bin ∘ tip) _,_ t tᴾ (upgrade u) (upgradeᴾ Q u uᴾ)

bu'ᴾ : (Q : ∀ {ys} → P ys → Set)
       (f : ∀ {ys} → Drop 1 P ys → P ys) → (∀ {ys} {ps : Drop 1 P ys} → All Q ps → Q (f ps))
     → (n : ℕ) (t : Drop n P xs) → All Q t → Q (bu' f n t)
bu'ᴾ Q f fᴾ  zero   t tᴾ = unTipᴾ Q t tᴾ
bu'ᴾ Q f fᴾ (suc n) t tᴾ = bu'ᴾ Q f fᴾ n (map f (upgrade t)) (mapᴾ (All Q) Q f fᴾ (upgrade t) (upgradeᴾ Q t tᴾ))

basement'ᴾ : {P : List A → Set} (Q : ∀ {ys} → P ys → Set) (xs : List A) {r : ℕ} (l : length xs ≤ r)
           → All Q (basement' {A} {P} xs l)
basement'ᴾ Q []       _       = tt
basement'ᴾ Q (x ∷ xs) (s≤s l) = basement'ᴾ Q xs l , basement'ᴾ Q xs (m≤n⇒m≤1+n l)

basementᴾ : {P : List A → Set} (Q : ∀ {ys} → P ys → Set) (xs : List A)
          → All Q (basement {A} {P} xs)
basementᴾ Q xs = basement'ᴾ Q xs ≤-refl

buᴾ : UnaryParametricity bu
buᴾ {A} {P} Q {f} g {xs} = bu'ᴾ Q f g _ (basement xs) (basementᴾ Q xs)

-- Equality between the two algorithms

equality : (P : List A → Set) (f : ∀ {ys} → Drop 1 P ys → P ys) (xs : List A)
         → td P f xs ≡ bu P f xs
equality = uniqueness td bu (λ {_} {P} → td-computation {_} {P}) buᴾ
