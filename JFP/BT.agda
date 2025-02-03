-- Checked with Agda 2.7.0.1 and Standard Library 2.2

{-# OPTIONS --safe --large-indices --no-forced-argument-recursion #-}

open import Level using (Level; Setω)
open import Function using (_∘_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; pred; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; m≤n⇒m≤1+n)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Char using (Char)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

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
    idenR :                         DropR  zero   xs       xs
    dropR : DropR       n   xs ys → DropR (suc n) (x ∷ xs) ys
    keepR : DropR (suc  n)  xs ys → DropR (suc n) (x ∷ xs) (x ∷ ys)

  ImmediateSublistInduction : Set₁
  ImmediateSublistInduction = {A : Set} (P : List A → Set)
                            →  (∀ {ys} → (∀ {zs} → DropR 1 ys zs → P zs) → P ys)
                            →  (xs : List A) → P xs

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
  return x cont = cont x

  _>>=_ : Nondet A → (A → Nondet B) → Nondet B
  (mx >>= f) cont = mx (λ x → f x cont)

  fmap : (A → B) → Nondet A → Nondet B
  fmap f mx = mx >>= λ x → return (f x)

  mzero : Nondet A
  mzero cont = ∅

  mplus : Nondet A → Nondet A → Nondet A
  mplus mx my cont = mx cont ⊕ my cont

  drop : ℕ → List A → Nondet (List A)
  drop  zero   xs       = return xs
  drop (suc n) []       = mzero
  drop (suc n) (x ∷ xs) = mplus (drop n xs) (fmap (x ∷_) (drop (suc n) xs))

  -- drop : ℕ → List A → ∀ {ℓ} {R : Set ℓ} → ⦃ Monoid R ⦄ → (List A → R) → R
  -- drop  zero   xs       cont = cont xs
  -- drop (suc n) []       cont = ∅
  -- drop (suc n) (x ∷ xs) cont = drop n xs cont ⊕ drop (suc n) xs (cont ∘ (x ∷_))

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

decompose : (l : ℕ) (xs : List A) → suc l ≡ length xs
          → Drop 1 (λ ys → l ≡ length ys) xs
decompose  zero   (_ ∷ []) eq = bin (tip refl) nil
decompose (suc l) (_ ∷ xs) eq =
  let eq' = cong pred eq in bin (tip eq') (map (cong suc) (decompose l xs eq'))

module Compact-td where

  td : ImmediateSublistInduction
  td {A} P f xs = td' (length xs) xs refl
    where
      td' : (l : ℕ) (xs : List A) → l ≡ length xs → P xs
      td'  zero   [] eq = f nil
      td' (suc l) xs eq = f (map (td' l _) (decompose l xs eq))

td' : (∀ {ys} → Drop 1 P ys → P ys)
    → (l : ℕ) (xs : List A) → l ≡ length xs → P xs
td' f  zero   [] eq = f nil
td' f (suc l) xs eq = f (map (td' f l _) (decompose l xs eq))

td : ImmediateSublistInduction
td {A} P f xs = td' f (length xs) xs refl

--------
-- Section 4

zipWith : (∀ {ys} → P ys → P′ ys → P″ ys)
        →  ∀ {xs} → Drop n P xs → Drop n P′ xs → Drop n P″ xs
zipWith f (tip p)    (tip q)    = tip (f p q)
zipWith f  nil        nil       = nil
zipWith f (bin t t') (bin u u') = bin (zipWith f t u) (zipWith f t' u')

ground : Drop n (Drop 1 P) []
ground {n = zero } = tip nil
ground {n = suc _} = nil

upgrade : Drop (suc n) P xs → Drop n (Drop 1 P) xs
upgrade    nil                = ground
upgrade t@(bin   (tip _)   _) = tip t
upgrade   (bin    nil    nil) = bin ground nil
upgrade   (bin t@(bin _ _) u) = bin (upgrade t)
                                    (zipWith (bin ∘ tip) t (upgrade u))

blank' : (xs : List A) {r : ℕ} → length xs ≤ r → Drop (suc r) P xs
blank' []       _       = nil
blank' (x ∷ xs) (s≤s l) = bin (blank' xs l) (blank' xs (m≤n⇒m≤1+n l))

blank : (xs : List A) → Drop (suc (length xs)) P xs
blank xs = blank' xs ≤-refl

unTip : Drop 0 P xs → P xs
unTip (tip p) = p

module Compact-bu where

  bu : ImmediateSublistInduction
  bu P f = bu' _ ∘ blank
    where
      bu' : (n : ℕ) → Drop n P xs → P xs
      bu'  zero   = unTip
      bu' (suc n) = bu' n ∘ map f ∘ upgrade

bu' : (∀ {ys} → Drop 1 P ys → P ys)
    → (n : ℕ) → Drop n P xs → P xs
bu' f  zero   = unTip
bu' f (suc n) = bu' f n ∘ map f ∘ upgrade

bu : ImmediateSublistInduction
bu P f = bu' f _ ∘ blank

--------
-- Section 5

All : (∀ {ys} → P ys → Set) → Drop n P xs → Set
All Q (tip p)   = Q p
All Q  nil      = ⊤
All Q (bin t u) = All Q t × All Q u

Parametricity : ImmediateSublistInduction → Set₁
Parametricity ind =
  {A : Set} {P : List A → Set}                (Q : ∀ {ys} → P ys → Set)
          → {f : ∀ {ys} → Drop 1 P ys → P ys} (g : ∀ {ys} {ps : Drop 1 P ys} → All Q ps → Q (f ps))
          → {xs : List A} → Q (ind P f xs)

uniqueness' : (ind : ImmediateSublistInduction) → Parametricity ind
            → {A : Set} (P : List A → Set) (f : ∀ {ys} → Drop 1 P ys → P ys)
            → (xs : List A) (n : ℕ) (eq : n ≡ length xs)
            → ind P f xs ≡ td' f n xs eq
uniqueness' ind param {A} P f xs = param Q (λ qs l eq → g l _ eq _ qs)
  where
    Q : ∀ {ys} → P ys → Set
    Q {ys} p = (l : ℕ) (eq : l ≡ length ys) → p ≡ td' f l ys eq

    revcat : List A → List A → List A
    revcat []       ys = ys
    revcat (x ∷ xs) ys = revcat xs (x ∷ ys)

    h : {l : ℕ} {ys : List A} (zs : List A) (t : Drop 1 (P ∘ revcat zs) ys)
      → (eqs : Drop 1 (λ ys' → l ≡ length (revcat zs ys')) ys)
      → All Q t → t ≡ map (td' f l (revcat zs _)) eqs
    h zs  nil             nil               _        = refl
    h zs (bin (tip p) u) (bin (tip eq) eqs) (q , qs) =
      cong₂ (bin ∘ tip) (q _ eq) (h (_ ∷ zs) u eqs qs)

    g : (l : ℕ) (ys : List A) (eq : l ≡ length ys) (t : Drop 1 P ys)
      → All Q t → f t ≡ td' f l ys eq
    g  zero   [] eq nil qs = refl
    g (suc l) ys eq t   qs = cong f (h [] t (decompose l ys eq) qs)

uniqueness : (ind : ImmediateSublistInduction) → Parametricity ind
           → {A : Set} (P : List A → Set) (f : ∀ {ys} → Drop 1 P ys → P ys)
           → (xs : List A) → ind P f xs ≡ td P f xs
uniqueness ind param P f xs = uniqueness' ind param P f xs (length xs) refl

--------
-- Parametricity of bu

unTipᴾ : (Q : ∀ {ys} → P ys → Set) (t : Drop 0 P xs) → All Q t → Q (unTip t)
unTipᴾ Q (tip p) q = q

mapᴾ : (Q : ∀ {ys} → P ys → Set) (Q′ : ∀ {ys} → P′ ys → Set)
       (f : ∀ {ys} → P ys → P′ ys) → (∀ {ys} {p : P ys} → Q p → Q′ (f p))
     → (t : Drop n P xs) → All Q t → All Q′ (map f t)
mapᴾ Q Q′ f fᴾ (tip p)   q         = fᴾ q
mapᴾ Q Q′ f fᴾ  nil      _         = tt
mapᴾ Q Q′ f fᴾ (bin t u) (tᴾ , uᴾ) = mapᴾ Q Q′ f fᴾ t tᴾ , mapᴾ Q Q′ f fᴾ u uᴾ

groundᴾ : (Q : ∀ {ys} → P ys → Set) (n : ℕ) → All (All (λ {ys} → Q {ys})) (ground {n})
groundᴾ Q  zero   = tt
groundᴾ Q (suc _) = tt

zipWithᴾ : (Q : ∀ {ys} → P ys → Set) (Q′ : ∀ {ys} → P′ ys → Set) (Q″ : ∀ {ys} → P″ ys → Set)
           (f : ∀ {ys} → P ys → P′ ys → P″ ys) → (∀ {ys} {p : P ys} {p′ : P′ ys} → Q p → Q′ p′ → Q″ (f p p′))
         → ∀ {xs} → (t : Drop n P xs) → All Q t → (u : Drop n P′ xs) → All Q′ u → All Q″ (zipWith f t u)
zipWithᴾ Q Q′ Q″ f fᴾ (tip p)    q          (tip p')   q'         = fᴾ q q'
zipWithᴾ Q Q′ Q″ f fᴾ  nil       _           nil       _          = tt
zipWithᴾ Q Q′ Q″ f fᴾ (bin t t') (tᴾ , t'ᴾ) (bin u u') (uᴾ , u'ᴾ) = zipWithᴾ Q Q′ Q″ f fᴾ t  tᴾ  u  uᴾ ,
                                                                    zipWithᴾ Q Q′ Q″ f fᴾ t' t'ᴾ u' u'ᴾ

upgradeᴾ : (Q : ∀ {ys} → P ys → Set) (t : Drop (suc n) P xs) → All Q t → All (All Q) (upgrade t)
upgradeᴾ {n = n}     Q    nil                 tᴾ       = groundᴾ Q n
upgradeᴾ             Q t@(bin   (tip _)   u)  tᴾ       = tᴾ
upgradeᴾ {n = suc n} Q   (bin    nil    nil)  tᴾ       = groundᴾ Q n , tt
upgradeᴾ             Q   (bin t@(bin _ _) u) (tᴾ , uᴾ) =
  upgradeᴾ Q t tᴾ , zipWithᴾ Q (All Q) (All (λ {ys} → Q {ys})) (bin ∘ tip) _,_ t tᴾ (upgrade u) (upgradeᴾ Q u uᴾ)

bu'ᴾ : (Q : ∀ {ys} → P ys → Set)
       (f : ∀ {ys} → Drop 1 P ys → P ys) → (∀ {ys} {ps : Drop 1 P ys} → All Q ps → Q (f ps))
     → (n : ℕ) (t : Drop n P xs) → All Q t → Q (bu' f n t)
bu'ᴾ Q f fᴾ  zero   t tᴾ = unTipᴾ Q t tᴾ
bu'ᴾ Q f fᴾ (suc n) t tᴾ = bu'ᴾ Q f fᴾ n (map f (upgrade t)) (mapᴾ (All Q) Q f fᴾ (upgrade t) (upgradeᴾ Q t tᴾ))

blank'ᴾ : {P : List A → Set} (Q : ∀ {ys} → P ys → Set) (xs : List A) {r : ℕ} (l : length xs ≤ r)
        → All Q (blank' {A} {P} xs l)
blank'ᴾ Q []       _       = tt
blank'ᴾ Q (x ∷ xs) (s≤s l) = blank'ᴾ Q xs l , blank'ᴾ Q xs (m≤n⇒m≤1+n l)

blankᴾ : {P : List A → Set} (Q : ∀ {ys} → P ys → Set) (xs : List A)
       → All Q (blank {A} {P} xs)
blankᴾ Q xs = blank'ᴾ Q xs ≤-refl

buᴾ : Parametricity bu
buᴾ {A} {P} Q {f} g {xs} = bu'ᴾ Q f g _ (blank xs) (blankᴾ Q xs)

--------
-- Equality between the two algorithms

equality : (P : List A → Set) (f : ∀ {ys} → Drop 1 P ys → P ys) (xs : List A)
         → bu P f xs ≡ td P f xs
equality = uniqueness bu buᴾ
