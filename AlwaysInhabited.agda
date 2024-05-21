{-# OPTIONS --safe --large-indices --no-forced-argument-recursion #-}

open import Function
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec
open import Relation.Binary.PropositionalEquality

variable
  a b c : Set
  n k   : ℕ
  x     : a
  xs    : Vec a n
  p q r : a → Set

data BT : (n k : ℕ) → (Vec a k → Set) → Vec a n → Set where
  tipZ : p []                        → BT n        zero   p xs
  nil  : ⦃ n < suc k ⦄               → BT n       (suc k) p xs
  tipS : p xs                        → BT (suc k) (suc k) p xs
  bin  : ⦃ n > k ⦄
       → BT n (suc k) p           xs
       → BT n      k (p ∘ (x ∷_)) xs → BT (suc n) (suc k) p (x ∷ xs)

mapBT : (∀ {ys} → p ys → q ys) → ∀ {xs} → BT n k p xs → BT n k q xs
mapBT f  nil      = nil
mapBT f (tipZ x)  = tipZ (f x)
mapBT f (tipS x)  = tipS (f x)
mapBT f (bin t u) = bin  (mapBT f t) (mapBT f u)

unTip : BT n n p xs → p xs
unTip           (nil ⦃ n<n ⦄)     = ⊥-elim (<-irrefl refl n<n)
unTip {xs = []} (tipZ x)          = x
unTip           (tipS x)          = x
unTip           (bin ⦃ n>n ⦄ _ _) = ⊥-elim (<-irrefl refl n>n)

zipBTWith : (∀ {ys} → p ys → q ys → r ys) → ∀ {xs} → BT n k p xs → BT n k q xs → BT n k r xs
zipBTWith f (nil ⦃ n<k     ⦄)   nil              = nil ⦃ n<k ⦄
zipBTWith f (nil ⦃ 1+k<1+k ⦄)  (tipS _)          = ⊥-elim (<-irrefl refl 1+k<1+k)
zipBTWith f (nil ⦃ s≤s n<k ⦄)  (bin ⦃ n>k ⦄ _ _) = ⊥-elim (≤⇒≯ (<⇒≤ n<k) n>k)
zipBTWith f (tipZ x)           (tipZ y)          = tipZ (f x y)
zipBTWith f (tipS x)           (nil ⦃ 1+k<1+k ⦄) = ⊥-elim (<-irrefl refl 1+k<1+k)
zipBTWith f (tipS x)           (tipS y)          = tipS (f x y)
zipBTWith f (tipS x)           (bin ⦃ k>k ⦄ _ _) = ⊥-elim (1+n≰n k>k)
zipBTWith f (bin ⦃ n>k ⦄ _ _)  (nil ⦃ s≤s n<k ⦄) = ⊥-elim (≤⇒≯ (<⇒≤ n<k) n>k)
zipBTWith f (bin ⦃ n>n ⦄ t t') (tipS y)          = ⊥-elim (1+n≰n n>n)
zipBTWith f (bin ⦃ n>k ⦄ t t') (bin u u')        = bin ⦃ n>k ⦄ (zipBTWith f t u) (zipBTWith f t' u')

_∷ᴮᵀ_ : p xs → BT (1 + k) k (p ∘ (x ∷_)) xs → BT (2 + k) (1 + k) p (x ∷ xs)
p ∷ᴮᵀ t = bin ⦃ ≤-refl ⦄ (tipS p) t

retabulate : BT n k p xs → BT n (1 + k) (BT (1 + k) k p) xs
retabulate                  (nil ⦃ n<k ⦄)                              = nil ⦃ m≤n⇒m≤1+n n<k ⦄
retabulate {xs = []       } (tipZ y)                                   = nil ⦃ ≤-refl ⦄
retabulate {xs = _ ∷ []   } (tipZ y)                                   = tipS (tipZ y)
retabulate {xs = _ ∷ _ ∷ _} (tipZ y)                                   = bin ⦃ s≤s z≤n ⦄ (retabulate (tipZ y)) (tipZ (tipZ y))
retabulate                  (tipS y)                                   = nil ⦃ ≤-refl ⦄
retabulate (bin ⦃ n>k ⦄       (nil ⦃ n<1+k ⦄)     u                  ) = ⊥-elim (1+n≰n (≤-trans n<1+k n>k))
retabulate (bin               (tipS y)            u                  ) = tipS (y ∷ᴮᵀ u)
retabulate (bin ⦃ 1+n>1+k ⦄ t@(bin _ _)             (nil ⦃ 1+n<1+k ⦄)) = ⊥-elim (≤⇒≯ (<⇒≤ 1+n<1+k) 1+n>1+k)
retabulate (bin             t@(bin ⦃ n>0 ⦄ _ _)     (tipZ z)         ) = bin ⦃ s≤s n>0 ⦄ (retabulate t) (mapBT (_∷ᴮᵀ (tipZ z)) t)
retabulate (bin             t@(bin _ _)             (tipS _)         ) = nil ⦃ ≤-refl ⦄
retabulate (bin             t@(bin ⦃ n>1+k ⦄ _ _) u@(bin _ _)        ) = bin ⦃ s≤s n>1+k ⦄ (retabulate t) (zipBTWith _∷ᴮᵀ_ t (retabulate u))
