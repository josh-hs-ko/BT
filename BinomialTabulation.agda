-- Checked with Agda 2.6.4.1 and Standard Library 2.0

{-# OPTIONS --safe --large-indices --no-forced-argument-recursion #-}

module BinomialTabulation where

open import Function renaming (_$_ to infixr 5 _$_)
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec
open import Data.Char using (Char)
open import Relation.Binary.PropositionalEquality

variable
  a b c          : Set
  k m n          : ℕ
  x              : a
  xs ys          : Vec a k
  p p' q q' r r' : a → Set

module ShapeIndexing where

  data B : ℕ → ℕ → Set → Set where
    tipZ : a             → B n        zero   a
    tipS : a             → B (suc k) (suc k) a
    bin  : B n (suc k) a
         → B n      k  a → B (suc n) (suc k) a

  bounded : B n k a → k ≤ n
  bounded (tipZ _)  = z≤n
  bounded (tipS _)  = ≤-refl
  bounded (bin _ u) = s≤s (bounded u)

  unbounded : B k (suc k) a → ⊥
  unbounded (bin t u) = unbounded u

  mapB : (a → b) → B n k a → B n k b
  mapB f (tipZ x)  = tipZ (f x)
  mapB f (tipS x)  = tipS (f x)
  mapB f (bin t u) = bin (mapB f t) (mapB f u)

  unTipB : B n n a → a
  unTipB (tipZ x)  = x
  unTipB (tipS x)  = x
  unTipB (bin t _) = ⊥-elim (unbounded t)

  zipBWith : (a → b → c) → B n k a → B n k b → B n k c
  zipBWith f (tipZ x)   (tipZ y)   = tipZ (f x y)
  zipBWith f (tipS x)   u          = tipS (f x (unTipB u))
  zipBWith f (bin t _)  (tipS _)   = ⊥-elim (unbounded t)
  zipBWith f (bin t t') (bin u u') = bin (zipBWith f t u) (zipBWith f t' u')

  cd : 1 ≤ k → k < n → B n k a → B n (1 + k) (Vec a (1 + k))
  cd () _      (tipZ _)
  cd _ 1+k<1+k (tipS _) = ⊥-elim (<-irrefl refl 1+k<1+k)
  cd _ _             (bin   (tipS y  )   (tipZ z )) = tipS (y ∷ z ∷ [])
  cd _ _             (bin   (tipS y  ) u@(bin _ _)) = tipS (y ∷ unTip (cd (s≤s z≤n) ≤-refl u))
  cd _ _             (bin t@(bin t' _)   (tipZ z )) = bin (cd ≤-refl (s≤s (bounded t')) t) (mapB (_∷ (z ∷ [])) t)
  cd _ 2+n<2+n       (bin   (bin _ _ )   (tipS _ )) = ⊥-elim (<-irrefl refl 2+n<2+n)
  cd _ (s≤s 1+k<1+n) (bin t@(bin t' _) u@(bin _ _)) = bin (cd (s≤s z≤n) (s≤s (bounded t')) t) (zipBWith _∷_ t (cd (s≤s z≤n) 1+k<1+n u))

  -- end of module ShapeIndexing

module RestrictedSpecification where

  variable h : Vec a k → b

  data B' : (n k : ℕ) (b : Set) → (Vec a k → b) → Vec a n → Set where
    tipZ : (y : b) → y ≡ h []                    → B' n        zero   b h xs
    tipS : (y : b) → y ≡ h xs                    → B' (suc k) (suc k) b h xs
    bin  : B' n (suc k) b         h           xs
         → B' n      k  b (λ zs → h (x ∷ zs)) xs → B' (suc n) (suc k) b h (x ∷ xs)

  -- testB' : {b : Set} {h : Vec Char 2 → b} → B' 4 2 b h ('a' ∷ 'b' ∷ 'c' ∷ 'd' ∷ [])
  -- testB' = bin (bin (tipS {!   !} {!   !})
  --                   (bin (tipS {!   !} {!   !})
  --                        (tipZ {!   !} {!   !})))
  --              (bin (bin (tipS {!   !} {!   !})
  --                        (tipZ {!   !} {!   !}))
  --                   (tipZ {!   !} {!   !}))

  -- end of module RestrictedSpecification

data BT : (n k : ℕ) → (Vec a k → Set) → Vec a n → Set where
  tipZ : p []                               → BT n        zero   p xs
  tipS : p xs                               → BT (suc k) (suc k) p xs
  bin  : BT n (suc k)        p           xs
       → BT n      k (λ zs → p (x ∷ zs)) xs → BT (suc n) (suc k) p (x ∷ xs)

-- testBT : {p : Vec Char 2 → Set} → BT 4 2 p ('a' ∷ 'b' ∷ 'c' ∷ 'd' ∷ [])
-- testBT = bin (bin (tipS {!   !})
--                   (bin (tipS {!   !})
--                        (tipZ {!   !})))
--              (bin (bin (tipS {!   !})
--                        (tipZ {!   !}))
--                   (tipZ {!   !}))

bounded : BT n k p xs → k ≤ n
bounded (tipZ _)  = z≤n
bounded (tipS _)  = ≤-refl
bounded (bin _ u) = s≤s (bounded u)

unbounded : BT k (suc k) p xs → ⊥
unbounded (bin t u) = unbounded u

mapBT : (∀ {ys} → p ys → q ys) → ∀ {xs} → BT n k p xs → BT n k q xs
mapBT f (tipZ x)  = tipZ (f x)
mapBT f (tipS x)  = tipS (f x)
mapBT f (bin t u) = bin (mapBT f t) (mapBT f u)

unTip : BT n n p xs → p xs
unTip           (tipS x)  = x
unTip {xs = []} (tipZ x)  = x
unTip           (bin t _) = ⊥-elim (unbounded t)

zipBTWith : (∀ {ys} → p ys → q ys → r ys) → ∀ {xs} → BT n k p xs → BT n k q xs → BT n k r xs
zipBTWith f (tipZ x)   (tipZ y)   = tipZ (f x y)
zipBTWith f (tipS x)   u          = tipS (f x (unTip u))
zipBTWith f (bin t _ ) (tipS _)   = ⊥-elim (unbounded t)
zipBTWith f (bin t t') (bin u u') = bin (zipBTWith f t u) (zipBTWith f t' u')

_∷ᴮᵀ_ : p xs → BT (1 + k) k (p ∘ (x ∷_)) xs → BT (2 + k) (1 + k) p (x ∷ xs)
p ∷ᴮᵀ t = bin (tipS p) t

retabulate : k < n → BT n k p xs → BT n (1 + k) (BT (1 + k) k p) xs
retabulate            1+k<1+k (tipS _) = ⊥-elim (<-irrefl refl 1+k<1+k)
retabulate {xs = _ ∷ []   } _ (tipZ y) = tipS (tipZ y)
retabulate {xs = _ ∷ _ ∷ _} _ (tipZ y) = bin (retabulate (s≤s z≤n) (tipZ y)) (tipZ (tipZ y))
retabulate _             (bin   (tipS y  ) u          ) = tipS (y ∷ᴮᵀ u)
retabulate _             (bin t@(bin t' _)   (tipZ z )) = bin (retabulate (s≤s (bounded t')) t) (mapBT (_∷ᴮᵀ (tipZ z)) t)
retabulate 2+n<2+n       (bin   (bin _  _)   (tipS _ )) = ⊥-elim (<-irrefl refl 2+n<2+n)
retabulate (s≤s 1+k<1+n) (bin t@(bin t' _) u@(bin _ _)) = bin (retabulate (s≤s (bounded t')) t) (zipBTWith _∷ᴮᵀ_ t (retabulate 1+k<1+n u))

incr : suc m ≤′ n → m ≤′ n
incr  ≤′-refl    = ≤′-step ≤′-refl
incr (≤′-step d) = ≤′-step (incr d)

module Choose where

  data Exactly : a → Set where
    exactly : (x : a) → Exactly x

  mapExactly : (f : a → b) → Exactly x → Exactly (f x)
  mapExactly f (exactly x) = exactly (f x)

  choose : (n k : ℕ) → k ≤′ n → (xs : Vec a n) → BT n k Exactly xs
  choose _        zero   _           _        = tipZ (exactly [])
  choose (suc k) (suc k)  ≤′-refl    xs       = tipS (exactly xs)
  choose (suc n) (suc k) (≤′-step d) (x ∷ xs) = bin (choose n (suc k) d xs) (mapBT (mapExactly (x ∷_)) (choose n k (incr d) xs))

  toBTExactly : BT n k (const ⊤) xs → BT n k Exactly xs
  toBTExactly = mapBT (λ { {ys} tt → exactly ys })

  -- end of module Choose

blank' : (n k : ℕ) → k ≤′ n → {xs : Vec a n} → BT n k (const ⊤) xs
blank' _        zero   _                   = tipZ tt
blank' (suc k) (suc k)  ≤′-refl            = tipS tt
blank' (suc n) (suc k) (≤′-step d) {_ ∷ _} = bin (blank' n (suc k) d) (blank' n k (incr d))

module Monster where

  ImmediateSublistInduction : Set₁
  ImmediateSublistInduction =
    {a : Set} (s  : ∀ {k} → Vec a k → Set)
              (e  : s [])
              (g  : ∀ {k} → {ys : Vec a (1 + k)} → BT (1 + k) k s ys → s ys)
    {n : ℕ}   (xs : Vec a n) → s xs

  td : ImmediateSublistInduction
  td s e g {zero } [] = e
  td s e g {suc n} ys = g (mapBT (λ { {ys} tt → td s e g {n} ys}) (blank' (1 + n) n (≤′-step ≤′-refl)))

  -- end of module Monster

blank : (n k : ℕ) → k ≤′ n → {xs : Vec a n} → ⊤ → BT n k (const ⊤) xs
blank n k k≤n = const (blank' n k k≤n)

ImmediateSublistInduction : Set₁
ImmediateSublistInduction =
  {a : Set} (s : ∀ {k} → Vec a k → Set)
            (e : {ys : Vec a 0} → ⊤ → s ys)
            (g : ∀ {k} → {ys : Vec a (1 + k)} → BT (1 + k) k s ys → s ys)
            (n : ℕ) {xs : Vec a n} → ⊤ → s xs

td : ImmediateSublistInduction
td s e g  zero   = e
td s e g (suc n) = g ∘ mapBT (td s e g n) ∘ blank (1 + n) n (≤′-step ≤′-refl)

-- bu : ImmediateSublistInduction
-- bu s e g n = unTip ∘ loop 0 (≤⇒≤‴ z≤n) ∘ mapBT e ∘ blank n 0 (≤⇒≤′ z≤n)
--   where
--     loop : (k : ℕ) → k ≤‴ n → BT n k s xs → BT n n s xs
--     loop n  ≤‴-refl        = id
--     loop k (≤‴-step n≥1+k) = loop (1 + k) n≥1+k ∘ mapBT g ∘ retabulate (≤‴⇒≤ n≥1+k)

bu-loop : {s : ∀ {k} → Vec a k → Set} (g : ∀ {k} → {ys : Vec a (1 + k)} → BT (1 + k) k s ys → s ys) {n : ℕ}
          (k : ℕ) → k ≤‴ n → {xs : Vec a n} → BT n k s xs → BT n n s xs
bu-loop g n  ≤‴-refl        = id
bu-loop g k (≤‴-step n≥1+k) = bu-loop g (1 + k) n≥1+k ∘ mapBT g ∘ retabulate (≤‴⇒≤ n≥1+k)

bu : ImmediateSublistInduction
bu s e g n = unTip ∘ bu-loop g 0 (≤⇒≤‴ z≤n) ∘ mapBT e ∘ blank n 0 (≤⇒≤′ z≤n)

module ℕ-InductionPrinciple where

  ℕ-Induction : Set₁
  ℕ-Induction = (p  : ℕ → Set)
                (pz : p zero)
                (ps : ∀ {m} → p m → p (suc m))
                (n  : ℕ) → p n

  ind : ℕ-Induction
  ind P pz ps  zero   = pz
  ind P pz ps (suc n) = ps (ind P pz ps n)

  ℕ-Induction-unary-parametricity : ℕ-Induction → Set₁
  ℕ-Induction-unary-parametricity f =
      {p  : ℕ → Set}                 (q : ∀ {m} → p m → Set)
    → {pz : p zero}                  (qz : q pz)
    → {ps : ∀ {m} → p m → p (suc m)} (qs : ∀ {m} {x : p m} → q x → q (ps x))
    → {n  : ℕ} → q (f p pz ps n)

  ℕ-Induction-uniqueness-from-parametricity :
      (f : ℕ-Induction) → ℕ-Induction-unary-parametricity f
    → (P : ℕ → Set) (pz : P zero) (ps : ∀ {m} → P m → P (suc m)) (n : ℕ)
    → f P pz ps n ≡ ind P pz ps n
  ℕ-Induction-uniqueness-from-parametricity f param p pz ps n =
    param (λ {m} x → x ≡ ind p pz ps m) refl (cong ps)

  -- end of module ℕ-InductionPrinciple

BT' : ({ys : Vec a k} → p ys → Set) → BT n k p xs → Set
BT' q (tipZ x)  = q x
BT' q (tipS x)  = q x
BT' q (bin t u) = BT' q t × BT' q u

ISI-unary-parametricity : ImmediateSublistInduction → Set₁
ISI-unary-parametricity f =
  {a : Set} {s : ∀ {k} → Vec a k → Set}               (s' : ∀ {k} {ys : Vec a k} → s ys → Set)
            {e : {ys : Vec a 0} → ⊤ → s ys}           (e' : ∀ {ys} → s' (e {ys} tt))
            {g : ∀ {k ys} → BT (1 + k) k s ys → s ys} (g' : ∀ {k ys} {t : BT (1 + k) k s ys} → BT' s' t → s' (g t))
            {n : ℕ} {xs : Vec a n} → s' (f s e g n {xs} tt)

ISI-uniqueness-from-parametricity :
    (f : ImmediateSublistInduction) → ISI-unary-parametricity f
  → {a : Set} (s : ∀ {k} → Vec a k → Set)
  → (e : {ys : Vec a 0} → ⊤ → s ys) (g : ∀ {k ys} → BT (1 + k) k s ys → s ys) (n : ℕ) {xs : Vec a n}
  → f s e g n {xs} tt ≡ td s e g n {xs} tt
ISI-uniqueness-from-parametricity f param {a} s e g n =
  param (λ {m} {ys} x → x ≡ td s e g m {ys} tt) refl (λ t' → cong g (see-below s (λ xs → td s e g _ {xs} tt) _ t'))
  where
    see-below : (ss : Vec a k → Set) (h : (xs : Vec a k) → ss xs)
              → (ss' : BT (1 + k) k ss xs) → BT' (λ {ys} x → x ≡ h ys) ss'
              → ss' ≡ mapBT (λ {ys} _ → h ys) (blank' (suc k) k (≤′-step ≤′-refl))
    see-below ss h (tipZ _)          eq        = cong tipZ eq
    see-below ss h (bin (tipS _) t) (eq , ss') = cong₂ bin (cong tipS eq) (see-below (ss ∘ (_ ∷_)) (h ∘ (_ ∷_)) t ss')
    see-below ss h (bin (bin t _) _) _         = ⊥-elim (unbounded t)

Fam : Set → Set₁
Fam a = a → Set

_⇉_ : Fam a → Fam a → Set
p ⇉ q = ∀ {x} → p x → q x

infix 2 _⇉_

-- exponential objects
_⇒_ : Fam a → Fam a → Fam a
(p ⇒ q) x = p x → q x

infixr 3 _⇒_

IsProp : Set → Set
IsProp a = {x y : a} → x ≡ y

IsProp' : Set → Set
IsProp' a = (x y : a) → x ≡ y

BT-isProp' : (∀ {ys} → IsProp (p ys)) → IsProp' (BT n k p xs)
BT-isProp' p-isProp (tipZ _)  (tipZ _)    = cong tipZ p-isProp
BT-isProp' p-isProp (tipS _)  (tipS _)    = cong tipS p-isProp
BT-isProp' p-isProp (bin t u) (bin t' u') = cong₂ bin (BT-isProp' p-isProp t t')
                                                      (BT-isProp' p-isProp u u')
BT-isProp' p-isProp (tipS _)  (bin t' _)  = ⊥-elim (unbounded t')
BT-isProp' p-isProp (bin t _) (tipS _)    = ⊥-elim (unbounded t)

BT-isProp : (∀ {ys} → IsProp (p ys)) → IsProp (BT n k p xs)
BT-isProp p-isProp = BT-isProp' p-isProp _ _

rotation : ∀ {k<n k≤n k≤1+k 1+k≤n}
         → retabulate k<n (blank n k k≤n {xs} tt) ≡ mapBT (blank (1 + k) k k≤1+k) (blank n (1 + k) 1+k≤n tt)
rotation = BT-isProp (BT-isProp refl)

-- basic properties

cong-mapBT : {f g : p ⇉ q} → (∀ {ys} (x : p ys) → f x ≡ g x)
           → (t : BT n k p xs) → mapBT f t ≡ mapBT g t
cong-mapBT f≗g (tipZ x)  = cong tipZ (f≗g x)
cong-mapBT f≗g (tipS x)  = cong tipS (f≗g x)
cong-mapBT f≗g (bin t u) = cong₂ bin (cong-mapBT f≗g t) (cong-mapBT f≗g u)

mapBT-∘ : (f : q ⇉ r) (g : p ⇉ q)
        → (t : BT n k p xs) → mapBT (f ∘ g) $ t ≡ mapBT f ∘ mapBT g $ t
mapBT-∘ f g (tipZ _)  = refl
mapBT-∘ f g (tipS _)  = refl
mapBT-∘ f g (bin t u) = cong₂ bin (mapBT-∘ f g t) (mapBT-∘ f g u)

≤-isProp' : {m n : ℕ} → IsProp' (m ≤ n)
≤-isProp'  z≤n       z≤n       = refl
≤-isProp' (s≤s m≤n) (s≤s m≤n') = cong s≤s (≤-isProp' m≤n m≤n')

≤-isProp : {m n : ℕ} → IsProp (m ≤ n)
≤-isProp = ≤-isProp' _ _

-- naturality

unTip-natural : (h : p ⇉ q) {xs : Vec a n} (t : BT n n p xs)
              → h ∘ unTip $ t ≡ unTip ∘ mapBT h $ t
unTip-natural h      (tipS p)  = refl
unTip-natural h {[]} (tipZ p)  = refl
unTip-natural h      (bin t _) = ⊥-elim (unbounded t)

zipBTWith-natural :
    (P : p ⇉ p') (Q : q ⇉ q') (R : r ⇉ r')
    (f : p ⇉ q ⇒ r) (f' : p' ⇉ q' ⇒ r')
  → ({xs : Vec a k} {x : p xs} {y : q xs} → R (f x y) ≡ f' (P x) (Q y))
  →  {xs : Vec a n} (t : BT n k p xs) (u : BT n k q xs)
  → mapBT R (zipBTWith f t u) ≡ zipBTWith f' (mapBT P t) (mapBT Q u)
zipBTWith-natural P Q R f f' f∼f' (tipZ x)   (tipZ y)   = cong tipZ f∼f'
zipBTWith-natural P Q R f f' f∼f' (tipS x)   u          = cong tipS (trans f∼f' (cong (f' (P x)) (unTip-natural Q u)))
zipBTWith-natural P Q R f f' f∼f' (bin t _)  (tipS _)   = ⊥-elim (unbounded t)
zipBTWith-natural P Q R f f' f∼f' (bin t t') (bin u u') = cong₂ bin (zipBTWith-natural P Q R f f' f∼f' t  u )
                                                                    (zipBTWith-natural P Q R f f' f∼f' t' u')

-- retabulate-natural : (k<n : k < n) {xs : Vec a n} (h : p ⇉ q) (t : BT n k p xs)
--                    → mapBT (mapBT h) ∘ retabulate k<n $ t ≡ retabulate k<n ∘ mapBT h $ t
-- retabulate-natural 1+n<1+n       h (tipS p)                       = ⊥-elim (<-irrefl refl 1+n<1+n)
-- retabulate-natural _ {_ ∷ []   } h (tipZ p)                       = refl
-- retabulate-natural _ {_ ∷ _ ∷ _} h (tipZ p)                       = cong₂ bin (retabulate-natural 1+n>0 h (tipZ p)) refl where 1+n>0 = s≤s z≤n
-- retabulate-natural _             h (bin   (tipS p)   u)           = refl
-- retabulate-natural _             h (bin t@(bin t' _)   (tipZ q))  = cong₂ bin (trans (retabulate-natural 1+n>1 h t) (cong (λ ineq → retabulate ineq (mapBT h t)) ≤-isProp)) (trans (sym (mapBT-∘ (mapBT h) (λ p → bin (tipS p) (tipZ q)) t)) (mapBT-∘ (λ p → bin (tipS p) (tipZ (h q))) h t)) where 1+n>1 = s≤s (bounded t')
-- retabulate-natural _             h (bin t@(bin _  _)   (tipS q))  = ⊥-elim (unbounded t)
-- retabulate-natural (s≤s 1+k<1+n) h (bin t@(bin t' _) u@(bin _ _)) = cong₂ bin (trans (retabulate-natural 1+n>2+k h t) (cong (λ ineq → retabulate ineq (mapBT h t)) ≤-isProp)) (trans (zipBTWith-natural h (mapBT h) (mapBT h) (λ p → bin (tipS p)) (λ p → bin (tipS p)) refl t (retabulate 1+n>1+k u)) (cong (zipBTWith (λ p → bin (tipS p)) (mapBT h t)) (retabulate-natural 1+n>1+k h u))) where 1+n>2+k = s≤s (bounded t')






-- --------
-- -- Notations for understanding indexed types as if they were simple types
-- -- Or: switching to the categories of families

-- ∀[_]_⇉_ : (A : Set) → Fam A → Fam A → Set
-- ∀[ A ] P ⇉ Q = P ⇉ Q

-- infix 2 ∀[_]_⇉_

-- --------
-- -- Correctness: separating both algorithms into production and consumption phases

-- module Production where

--   tdRec : (n : ℕ) → Fam (Vec A n)
--   tdRec  zero   = const ⊤
--   tdRec (suc n) = BT (suc n) n (tdRec n)

--   td-construct : (n : ℕ) → ∀[ Vec A n ] const ⊤ ⇉ tdRec n
--   td-construct  zero   = id
--   td-construct (suc n) = mapBT (td-construct n) ∘ blanks (suc n) n 1+n≥n
--     where 1+n≥n = ≤′-step ≤′-refl

--   tdRec-isProp : (n : ℕ) {xs : Vec A n} → IsProp (tdRec n xs)
--   tdRec-isProp  zero   = refl
--   tdRec-isProp (suc n) = BT-isProp (tdRec-isProp n)

--   buRec : n ≥‴ k → Fam (Vec A k) → Fam (Vec A n)
--   buRec          ≤‴-refl        = id
--   buRec {k = k} (≤‴-step n≥1+k) = buRec n≥1+k ∘ BT (suc k) k

--   bu-construct-loop : (n≥k : n ≥‴ k) → BT n k P ⇉ BT n n (buRec n≥k P)
--   bu-construct-loop  ≤‴-refl        = id
--   bu-construct-loop (≤‴-step n≥1+k) = bu-construct-loop n≥1+k ∘ retabulate (≤‴⇒≤ n≥1+k)

--   bu-construct : (n : ℕ) → ∀[ Vec A n ] const ⊤ ⇉ buRec (≤⇒≤‴ z≤n) (const ⊤)
--   bu-construct n = unTip ∘ bu-construct-loop (≤⇒≤‴ z≤n) ∘ blanks n 0 (≤⇒≤′ z≤n)

--   map-buRec : (n≥k : n ≥‴ k) → P ⇉ Q → buRec n≥k P ⇉ buRec n≥k Q
--   map-buRec  ≤‴-refl        f = f
--   map-buRec (≤‴-step n≥1+k) f = map-buRec n≥1+k (mapBT f)

--   cong-map-buRec :
--       (n≥k : n ≥‴ k) {f g : P ⇉ Q} → (∀ {ys} (p : P ys) → f p ≡ g p)
--     → {xs : Vec A n} (t : buRec n≥k P xs) → map-buRec n≥k f t ≡ map-buRec n≥k g t
--   cong-map-buRec  ≤‴-refl        f≗g t = f≗g t
--   cong-map-buRec (≤‴-step n≥1+k) f≗g t = cong-map-buRec n≥1+k (cong-mapBT f≗g) t

--   map-buRec-∘ : (n≥k : n ≥‴ k) (f : Q ⇉ R) (g : P ⇉ Q)
--               → {xs : Vec A n} (t : buRec n≥k P xs)
--               → map-buRec n≥k (f ∘ g) $ t ≡ map-buRec n≥k f ∘ map-buRec n≥k g $ t
--   map-buRec-∘  ≤‴-refl        f g t = refl
--   map-buRec-∘ (≤‴-step n≥1+k) f g t =
--     trans (cong-map-buRec n≥1+k (mapBT-∘ f g) t) (map-buRec-∘ n≥1+k (mapBT f) (mapBT g) t)

--   bu-construct-loop-natural :
--       (n≥k : n ≥‴ k) (h : P ⇉ Q) {xs : Vec A n} (t : BT n k P xs)
--     → mapBT (map-buRec n≥k h) ∘ bu-construct-loop n≥k $ t ≡ bu-construct-loop n≥k ∘ mapBT h $ t
--   bu-construct-loop-natural  ≤‴-refl        h t = refl
--   bu-construct-loop-natural (≤‴-step n≥1+k) h t =
--     begin
--       mapBT (map-buRec (≤‴-step n≥1+k) h) ∘ bu-construct-loop (≤‴-step n≥1+k)               $ t
--         ≡⟨ refl ⟩
--       mapBT (map-buRec n≥1+k (mapBT h)) ∘ bu-construct-loop n≥1+k ∘ retabulate (≤‴⇒≤ n≥1+k) $ t
--         ≡⟨ bu-construct-loop-natural n≥1+k (mapBT h) _ ⟩
--       bu-construct-loop n≥1+k ∘ mapBT (mapBT h) ∘ retabulate (≤‴⇒≤ n≥1+k)                   $ t
--         ≡⟨ cong (bu-construct-loop n≥1+k) (retabulate-natural (≤‴⇒≤ n≥1+k) h t) ⟩
--       bu-construct-loop n≥1+k ∘ retabulate (≤‴⇒≤ n≥1+k) ∘ mapBT h                           $ t
--         ≡⟨ refl ⟩
--       bu-construct-loop (≤‴-step n≥1+k) ∘ mapBT h                                           $ t
--     ∎
--     where open ≡-Reasoning

--   unTip∘bu-construct-loop-natural :
--       (n≥k : n ≥‴ k) (h : P ⇉ Q) {xs : Vec A n} (t : BT n k P xs)
--     → map-buRec n≥k h ∘ unTip ∘ bu-construct-loop n≥k           $ t
--     ≡                   unTip ∘ bu-construct-loop n≥k ∘ mapBT h $ t
--   unTip∘bu-construct-loop-natural n≥k h t =
--       begin
--         map-buRec n≥k h ∘ unTip ∘ bu-construct-loop n≥k         $ t
--           ≡⟨ unTip-natural (map-buRec n≥k h) (bu-construct-loop n≥k t) ⟩
--         unTip ∘ mapBT (map-buRec n≥k h) ∘ bu-construct-loop n≥k $ t
--           ≡⟨ cong unTip (bu-construct-loop-natural n≥k h _) ⟩
--         unTip ∘ bu-construct-loop n≥k ∘ mapBT h                 $ t
--       ∎
--     where open ≡-Reasoning

--   overall : {A A' B : Set}
--           → (f : A → B) (f' : A' → B)
--           → ((Σ[ X ∈ Set ] (X → B)) ∋ (A , f)) ≡ (A' , f')
--           → IsProp A
--           → (a : A) (a' : A') → f a ≡ f' a'
--   overall f .f refl A-isProp a a' = cong f A-isProp

-- module Consumption-and-Correctness
--   {A : Set} (S : {k : ℕ} → Fam (Vec A k))
--   (e : const ⊤ ⇉ S {0}) (g : {k : ℕ} → BT (suc k) k S ⇉ S)
--   where

--   open Algorithms S e g
--   open Production

--   td-demolish : (n : ℕ) → tdRec n ⇉ S
--   td-demolish  zero   = e
--   td-demolish (suc n) = g ∘ mapBT (td-demolish n)

--   td-separation : (n : ℕ) {xs : Vec A n}
--                 → td n {xs} $ tt ≡ td-demolish n ∘ td-construct n $ tt
--   td-separation  zero   = refl
--   td-separation (suc n) =
--     begin
--       td (suc n)                                                                  $ tt
--         ≡⟨ refl ⟩
--       g ∘ mapBT (td n) ∘ blanks (suc n) n 1+n≥n                                   $ tt
--         ≡⟨ cong g (cong-mapBT (λ _ → td-separation n) _) ⟩
--       g ∘ mapBT (td-demolish n ∘ td-construct n) ∘ blanks (suc n) n 1+n≥n         $ tt
--         ≡⟨ cong g (mapBT-∘ (td-demolish n) (td-construct n) _) ⟩
--       g ∘ mapBT (td-demolish n) ∘ mapBT (td-construct n) ∘ blanks (suc n) n 1+n≥n $ tt
--         ≡⟨ refl ⟩
--       td-demolish (suc n) ∘ td-construct (suc n)                                  $ tt
--     ∎
--     where 1+n≥n = ≤′-step ≤′-refl
--           open ≡-Reasoning

--   bu-demolish-loop : (n≥k : n ≥‴ k) → buRec n≥k S ⇉ S
--   bu-demolish-loop  ≤‴-refl        = id
--   bu-demolish-loop (≤‴-step n≥1+k) = bu-demolish-loop n≥1+k ∘ map-buRec n≥1+k g

--   bu-demolish : (n : ℕ) → ∀[ Vec A n ] buRec (≤⇒≤‴ z≤n) (const ⊤) ⇉ S
--   bu-demolish n = bu-demolish-loop n≥0 ∘ map-buRec n≥0 e
--     where n≥0 = ≤⇒≤‴ z≤n

--   bu-loop-separation :
--       (n≥k : n ≥‴ k)
--     → {xs : Vec A n} (t : BT n k S xs)
--     → unTip ∘ bu-loop n≥k $ t ≡ bu-demolish-loop n≥k ∘ unTip ∘ bu-construct-loop n≥k $ t
--   bu-loop-separation  ≤‴-refl        t = refl
--   bu-loop-separation (≤‴-step n≥1+k) t =
--     begin
--       unTip ∘ bu-loop (≤‴-step n≥1+k)                                                                        $ t
--         ≡⟨ refl ⟩
--       unTip ∘ bu-loop n≥1+k ∘ mapBT g ∘ retabulate (≤‴⇒≤ n≥1+k)                                              $ t
--         ≡⟨ bu-loop-separation n≥1+k _ ⟩
--       bu-demolish-loop n≥1+k ∘ unTip ∘ bu-construct-loop n≥1+k ∘ mapBT g ∘ retabulate (≤‴⇒≤ n≥1+k)           $ t
--         ≡⟨ cong (bu-demolish-loop n≥1+k) (sym (unTip∘bu-construct-loop-natural n≥1+k g _)) ⟩
--       bu-demolish-loop n≥1+k ∘ map-buRec n≥1+k g ∘ unTip ∘ bu-construct-loop n≥1+k ∘ retabulate (≤‴⇒≤ n≥1+k) $ t
--         ≡⟨ refl ⟩
--       bu-demolish-loop (≤‴-step n≥1+k) ∘ unTip ∘ bu-construct-loop (≤‴-step n≥1+k)                           $ t
--     ∎
--     where open ≡-Reasoning

--   bu-separation : (n : ℕ) {xs : Vec A n} → bu n {xs} $ tt ≡ bu-demolish n ∘ bu-construct n $ tt
--   bu-separation n =
--     begin
--       bu n                                                                                           $ tt
--         ≡⟨ refl ⟩
--       unTip ∘ bu-loop n≥0 ∘ mapBT e ∘ blanks n 0 (≤⇒≤′ z≤n)                                          $ tt
--         ≡⟨ bu-loop-separation n≥0 _ ⟩
--       bu-demolish-loop n≥0 ∘ unTip ∘ bu-construct-loop n≥0 ∘ mapBT e ∘ blanks n 0 (≤⇒≤′ z≤n)         $ tt
--         ≡⟨ cong (bu-demolish-loop n≥0) (sym (unTip∘bu-construct-loop-natural n≥0 e _)) ⟩
--       bu-demolish-loop n≥0 ∘ map-buRec n≥0 e ∘ unTip ∘ bu-construct-loop n≥0 ∘ blanks n 0 (≤⇒≤′ z≤n) $ tt
--         ≡⟨ refl ⟩
--       bu-demolish n ∘ bu-construct n                                                                 $ tt
--     ∎
--     where n≥0 = ≤⇒≤‴ z≤n
--           open ≡-Reasoning

--   bu-demolish-loop' : (n≥k : n ≥‴ k) → R ⇉ S → buRec n≥k R ⇉ S
--   bu-demolish-loop'  ≤‴-refl        h = h
--   bu-demolish-loop' (≤‴-step n≥1+k) h = bu-demolish-loop' n≥1+k (g ∘ mapBT h)

--   bu-demolish' : (n : ℕ) → ∀[ Vec A n ] buRec (≤⇒≤‴ z≤n) (const ⊤) ⇉ S
--   bu-demolish' n = bu-demolish-loop' (≤⇒≤‴ z≤n) e

--   bu-demolish-loop-equiv :
--       (n≥k : n ≥‴ k) (h : R ⇉ S) {xs : Vec A n} (r : buRec n≥k R xs)
--     → bu-demolish-loop' n≥k h $ r ≡ bu-demolish-loop n≥k ∘ map-buRec n≥k h $ r
--   bu-demolish-loop-equiv  ≤‴-refl        h r = refl
--   bu-demolish-loop-equiv (≤‴-step n≥1+k) h r =
--     begin
--       bu-demolish-loop' (≤‴-step n≥1+k) h                                    $ r
--         ≡⟨ refl ⟩
--       bu-demolish-loop' n≥1+k (g ∘ mapBT h)                                  $ r
--         ≡⟨ bu-demolish-loop-equiv n≥1+k (g ∘ mapBT h) _ ⟩
--       bu-demolish-loop n≥1+k ∘ map-buRec n≥1+k (g ∘ mapBT h)                 $ r
--         ≡⟨ cong (bu-demolish-loop n≥1+k) (map-buRec-∘ n≥1+k g (mapBT h) _) ⟩
--       bu-demolish-loop n≥1+k ∘ map-buRec n≥1+k g ∘ map-buRec n≥1+k (mapBT h) $ r
--         ≡⟨ refl ⟩
--       bu-demolish-loop (≤‴-step n≥1+k) ∘ map-buRec (≤‴-step n≥1+k) h         $ r
--     ∎
--     where open ≡-Reasoning

--   bu-demolish-equiv :
--       (n : ℕ) {xs : Vec A n} (r : buRec (≤⇒≤‴ z≤n) (const ⊤) xs)
--     → bu-demolish' n r ≡ bu-demolish n r
--   bu-demolish-equiv n = bu-demolish-loop-equiv (≤⇒≤‴ z≤n) e

--   td≗bu-demolish :
--       (n≥k : n ≥‴ k) {xs : Vec A n}
--     → ((Σ[ X ∈ Set ] (X → S xs))
--       ∋ (tdRec n xs             , td-demolish n))
--       ≡ (buRec n≥k (tdRec k) xs , bu-demolish-loop' n≥k (td-demolish k))
--   td≗bu-demolish  ≤‴-refl        = refl
--   td≗bu-demolish (≤‴-step n≥1+k) = td≗bu-demolish n≥1+k

--   td≗bu : (n : ℕ) {xs : Vec A n} → td n {xs} $ tt ≡ bu n $ tt
--   td≗bu n =
--     begin
--       td n                            $ tt
--         ≡⟨ td-separation n ⟩
--       td-demolish n ∘ td-construct n  $ tt
--         ≡⟨ overall (td-demolish n) (bu-demolish-loop' n≥0 e) (td≗bu-demolish n≥0)
--              (tdRec-isProp n) (td-construct n tt) (bu-construct n tt) ⟩
--       bu-demolish' n ∘ bu-construct n $ tt
--         ≡⟨ bu-demolish-equiv n _ ⟩
--       bu-demolish n ∘ bu-construct n  $ tt
--         ≡⟨ sym (bu-separation n) ⟩
--       bu n                            $ tt
--     ∎
--     where n≥0 = ≤⇒≤‴ z≤n
--           open ≡-Reasoning
