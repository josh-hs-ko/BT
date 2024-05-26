{-# OPTIONS --safe --large-indices --no-forced-argument-recursion #-}

open import Function
open import Data.Unit
open import Data.Empty.Irrelevant
open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec
open import Relation.Binary.PropositionalEquality

variable
  a b c : Set
  k m n : ℕ
  x     : a
  xs    : Vec a n
  p q r : a → Set

data BT : (n k : ℕ) → (Vec a k → Set) → Vec a n → Set where
  tipZ : p []                        → BT n        zero   p xs
  nil  : .⦃ n < suc k ⦄              → BT n       (suc k) p xs
  tipS : p xs                        → BT (suc k) (suc k) p xs
  bin  : .⦃ n > k ⦄
       → BT n (suc k) p           xs
       → BT n      k (p ∘ (x ∷_)) xs → BT (suc n) (suc k) p (x ∷ xs)

module ComparisonWithChoose where

  open import Data.List
  open import Relation.Binary.Definitions

  pure : a → List a
  pure x = x ∷ []

  _<$>_ : (a → b) → List a → List b
  f <$> xs = Data.List.map f xs

  empty : List a
  empty = []

  _<|>_ : List a → List a → List a
  _<|>_ = Data.List._++_

  choose : (n k : ℕ) → Vec a n → List (Vec a k)
  choose n        zero   xs       = pure []
  choose n       (suc k) xs       with <-cmp n (suc k)
  choose n       (suc k) xs       | tri< n<sk _ _      = empty
  choose (suc k) (suc k) xs       | tri≈ _ refl _      = pure xs
  choose (suc n) (suc k) (x ∷ xs) | tri> _ _ (s≤s n>k) = choose n (suc k) xs <|> ((x ∷_) <$> choose n k xs)

mapBT : (∀ {ys} → p ys → q ys) → ∀ {xs} → BT n k p xs → BT n k q xs
mapBT f (tipZ z)  = tipZ (f z)
mapBT f  nil      = nil
mapBT f (tipS z)  = tipS (f z)
mapBT f (bin t u) = bin (mapBT f t) (mapBT f u)

unTip : BT n n p xs → p xs
unTip           (tipS y)  = y
unTip {xs = []} (tipZ y)  = y
-- impossible cases
unTip            nil      = ⊥-elim (<-irrefl refl it)
unTip           (bin _ _) = ⊥-elim (<-irrefl refl it)  -- immediately refutable

zipBTWith : (∀ {ys} → p ys → q ys → r ys) → ∀ {xs} → BT n k p xs → BT n k q xs → BT n k r xs
zipBTWith f (tipZ z)   (tipZ w)   = tipZ (f z w)
zipBTWith f  nil        nil       = nil  -- irrelevance matters to instance resolution
zipBTWith f (tipS z)   (tipS w)   = tipS (f z w)
zipBTWith f (bin t t') (bin u u') = bin (zipBTWith f t u) (zipBTWith f t' u')
-- impossible cases
zipBTWith f  nil       (tipS _)   = ⊥-elim (<-irrefl refl it)  -- SMT solving?
zipBTWith f  nil       (bin _ _)  = ⊥-elim (≤⇒≯ (<⇒≤ (≤-pred it)) it)
zipBTWith f (tipS _)    nil       = ⊥-elim (<-irrefl refl it)
zipBTWith f (tipS _)   (bin _ _)  = ⊥-elim (1+n≰n it)
zipBTWith f (bin _ _)   nil       = ⊥-elim (≤⇒≯ (<⇒≤ it) (≤-pred it))
zipBTWith f (bin _ _)  (tipS _)   = ⊥-elim (1+n≰n it)

instance
  _ : n ≤ n
  _ = ≤-refl

_∷ᴮᵀ_ : p xs → BT (1 + k) k (p ∘ (x ∷_)) xs → BT (2 + k) (1 + k) p (x ∷ xs)
y ∷ᴮᵀ t = bin (tipS y) t

retabulate : BT n k p xs → BT n (1 + k) (BT (1 + k) k p) xs
retabulate (tipZ y)                        = level-one _ y
  where
    level-one : (xs : Vec a n) → p [] → BT n 1 (BT 1 0 p) xs
    level-one []          y = nil
    level-one (_ ∷ [])    y = tipS (tipZ y)
    level-one (_ ∷ _ ∷ _) y = bin ⦃ s≤s z≤n ⦄ (level-one _ y) (tipZ (tipZ y))
retabulate  nil                            = nil ⦃ m≤n⇒m≤1+n it ⦄
retabulate (tipS y)                        = nil
retabulate (bin   (tipS y)    u          ) = tipS (y ∷ᴮᵀ u)
retabulate (bin t@(bin _ _)     (tipZ z) ) = bin ⦃ s≤s it ⦄ (retabulate t) (mapBT (_∷ᴮᵀ (tipZ z)) t)
retabulate (bin t@(bin _ _)     (tipS _) ) = nil
retabulate (bin t@(bin _ _)   u@(bin _ _)) = bin ⦃ s≤s it ⦄ (retabulate t) (zipBTWith _∷ᴮᵀ_ t (retabulate u))
-- impossible cases
retabulate (bin   (nil ⦃ l ⦄) u          ) = ⊥-elim (1+n≰n (≤-trans l it))
retabulate (bin t@(bin _ _)      nil     ) = ⊥-elim (≤⇒≯ (<⇒≤ it) it)

blank : ⊤ → BT (1 + k) k (const ⊤) xs
blank {k = zero }              _ = tipZ tt
blank {k = suc _} {xs = _ ∷ _} _ = tt ∷ᴮᵀ blank _

ImmediateSublistInduction : Set₁
ImmediateSublistInduction =
  {a : Set} (p : ∀ {k} → Vec a k → Set)
            (e : {ys : Vec a 0} → ⊤ → p ys)
            (g : ∀ {k} {ys : Vec a (1 + k)} → BT (1 + k) k p ys → p ys)
            (n : ℕ) {xs : Vec a n} → ⊤ → p xs

td : ImmediateSublistInduction
td p e g  zero   = e
td p e g (suc n) = g ∘ mapBT (td p e g n) ∘ blank

bu : ImmediateSublistInduction
bu p e g n = unTip ∘ loop (≤⇒≤‴ z≤n) ∘ tipZ ∘ e
  where
    loop : k ≤‴ n → BT n k p xs → BT n n p xs
    loop  ≤‴-refl    = id
    loop (≤‴-step d) = loop d ∘ mapBT g ∘ retabulate
