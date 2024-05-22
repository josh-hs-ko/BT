{-# OPTIONS --safe --large-indices --no-forced-argument-recursion #-}

open import Function
open import Data.Empty.Irrelevant
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
  nil  : .⦃ n < suc k ⦄              → BT n       (suc k) p xs
  tipS : p xs                        → BT (suc k) (suc k) p xs
  bin  : .⦃ n > k ⦄ -- suc n > suc k
       → BT n (suc k) p           xs
       → BT n      k (p ∘ (x ∷_)) xs → BT (suc n) (suc k) p (x ∷ xs)

mapBT : (∀ {ys} → p ys → q ys) → ∀ {xs} → BT n k p xs → BT n k q xs
mapBT f  nil      = nil
mapBT f (tipZ x)  = tipZ (f x)
mapBT f (tipS x)  = tipS (f x)
mapBT f (bin t u) = bin (mapBT f t) (mapBT f u)

unTip : BT n n p xs → p xs
unTip           (tipS x)  = x
unTip {xs = []} (tipZ x)  = x
-- impossible cases
unTip            nil      = ⊥-elim (<-irrefl refl it)
unTip           (bin _ _) = ⊥-elim (<-irrefl refl it)

zipBTWith : (∀ {ys} → p ys → q ys → r ys) → ∀ {xs} → BT n k p xs → BT n k q xs → BT n k r xs
zipBTWith f  nil        nil       = nil
zipBTWith f (tipZ x)   (tipZ y)   = tipZ (f x y)
zipBTWith f (tipS x)   (tipS y)   = tipS (f x y)
zipBTWith f (bin t t') (bin u u') = bin (zipBTWith f t u) (zipBTWith f t' u')
-- impossible cases
zipBTWith f  nil       (tipS _)   = ⊥-elim (<-irrefl refl it)
zipBTWith f  nil       (bin _ _)  = ⊥-elim (≤⇒≯ (<⇒≤ (≤-pred it)) it)
zipBTWith f (tipS _)    nil       = ⊥-elim (<-irrefl refl it)
zipBTWith f (tipS _)   (bin _ _)  = ⊥-elim (1+n≰n it)
zipBTWith f (bin _ _)   nil       = ⊥-elim (≤⇒≯ (<⇒≤ it) (≤-pred it))
zipBTWith f (bin _ _)  (tipS _)   = ⊥-elim (1+n≰n it)

_∷ᴮᵀ_ : p xs → BT (1 + k) k (p ∘ (x ∷_)) xs → BT (2 + k) (1 + k) p (x ∷ xs)
y ∷ᴮᵀ t = bin ⦃ ≤-refl ⦄ (tipS y) t

retabulate : BT n k p xs → BT n (1 + k) (BT (1 + k) k p) xs
retabulate                   nil         = nil ⦃ m≤n⇒m≤1+n it ⦄
retabulate {xs = []       } (tipZ y)     = nil ⦃ ≤-refl ⦄
retabulate {xs = _ ∷ []   } (tipZ y)     = tipS (tipZ y)
retabulate {xs = _ ∷ _ ∷ _} (tipZ y)     = bin ⦃ s≤s z≤n ⦄ (retabulate (tipZ y)) (tipZ (tipZ y))
retabulate                  (tipS y)     = nil ⦃ ≤-refl ⦄
retabulate (bin (tipS y)    u          ) = tipS (y ∷ᴮᵀ u)
retabulate (bin t@(bin _ _)   (tipZ z) ) = bin ⦃ s≤s it ⦄ (retabulate t) (mapBT (_∷ᴮᵀ (tipZ z)) t)
retabulate (bin t@(bin _ _)   (tipS _) ) = nil ⦃ ≤-refl ⦄
retabulate (bin t@(bin _ _) u@(bin _ _)) = bin ⦃ s≤s it ⦄ (retabulate t) (zipBTWith _∷ᴮᵀ_ t (retabulate u))
-- impossible cases
retabulate (bin (nil ⦃ l ⦄) u          ) = ⊥-elim (1+n≰n (≤-trans l it))
retabulate (bin t@(bin _ _)    nil     ) = ⊥-elim (≤⇒≯ (<⇒≤ it) it)
