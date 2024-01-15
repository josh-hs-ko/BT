{-# OPTIONS --safe --large-indices --no-forced-argument-recursion #-}

module BT where

open import Function renaming (_$_ to infixr 5 _$_)
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Product hiding (map)
open import Data.Nat
open import Data.Nat.Properties
open import Data.List as L hiding (map)
open import Data.Vec as V hiding (map)
open import Data.Vec.Relation.Unary.All hiding (map)
open import Relation.Binary.PropositionalEquality

variable
  A B C          : Set
  k m n          : ℕ
  x              : A
  xs ys          : Vec A _
  P P' Q Q' R R' : A → Set


--------
-- Notation for understanding indexed types as if they were simple types
-- Or: switching to the categories of families

_⇉_ : (A → Set) → (A → Set) → (A → Set)
(P ⇉ Q) x = P x → Q x

infixr 2 _⇉_

∀⟨_⟩[_] : (A : Set) → (A → Set) → Set
∀⟨ A ⟩[ P ] = {x : A} → P x

∀[_] : (A → Set) → Set
∀[ P ] = ∀ {x} → P x


--------
-- Binomial trees

data BT : (n k : ℕ) → (Vec A k → Set) → Vec A n → Set where
  TipZ : P []                        → BT      n   0      P xs
  TipS : P xs                        → BT (1 + n) (1 + n) P xs
  Bin  : BT n (1 + k) P           xs
       → BT n      k (λ ys → P (x ∷ ys)) xs → BT (1 + n) (1 + k) P (x ∷ xs)

-- testBT : (a b c d : A) → BT 4 2 P (a ∷ b ∷ c ∷ d ∷ [])
-- testBT a b c d =
--   Bin (Bin (TipS      {!   !})
--            (Bin (TipS {!   !})
--                 (TipZ {!   !})))
--       (Bin (Bin (TipS {!   !})
--                 (TipZ {!   !}))
--            (TipZ      {!   !}))

-- testBT² : (a b c : A) → BT 3 2 (BT 2 1 P) (a ∷ b ∷ c ∷ [])
-- testBT² a b c =
--   Bin (TipS      (Bin (TipS {!   !})
--                       (TipZ {!   !})))
--       (Bin (TipS (Bin (TipS {!   !})
--                       (TipZ {!   !})))
--            (TipZ (Bin (TipS {!   !})
--                       (TipZ {!   !}))))

bounded : BT n k P xs → n ≥ k
bounded (TipZ _)  = z≤n
bounded (TipS _)  = ≤-refl
bounded (Bin _ u) = s≤s (bounded u)

unbounded : BT n (suc n) P xs → ⊥
unbounded t = ≤⇒≯ (bounded t) ≤-refl

IsProp : Set → Set
IsProp A = (x y : A) → x ≡ y

IsProp-BT : (∀ {ys} → IsProp (P ys)) → ∀ {xs} → IsProp (BT n k P xs)
IsProp-BT IsProp-P (TipZ p)  (TipZ p')   = cong TipZ (IsProp-P p p')
IsProp-BT IsProp-P (TipS p)  (TipS p')   = cong TipS (IsProp-P p p')
IsProp-BT IsProp-P (Bin t u) (Bin t' u') = cong₂ Bin (IsProp-BT IsProp-P t t')
                                                     (IsProp-BT IsProp-P u u')
IsProp-BT IsProp-P (TipS p)  (Bin t' _)  = ⊥-elim (unbounded t')
IsProp-BT IsProp-P (Bin t u) (TipS p')   = ⊥-elim (unbounded t)

-- mapBT : (∀ {xs} → P xs → Q xs) → ∀ {xs} → BT n k P xs → BT n k Q xs
mapBT : ∀[ P ⇉ Q ] → ∀[ BT n k P ⇉ BT n k Q ]
mapBT f (TipZ p)  = TipZ (f p)
mapBT f (TipS p)  = TipS (f p)
mapBT f (Bin t u) = Bin (mapBT f t) (mapBT f u)

cong-mapBT : {f g : ∀[ P ⇉ Q ]} → (∀ {ys} (p : P ys) → f p ≡ g p)
           → (t : BT n k P xs) → mapBT f t ≡ mapBT g t
cong-mapBT f≗g (TipZ p)  = cong TipZ (f≗g p)
cong-mapBT f≗g (TipS p)  = cong TipS (f≗g p)
cong-mapBT f≗g (Bin t u) = cong₂ Bin (cong-mapBT f≗g t) (cong-mapBT f≗g u)

mapBT-∘ : (f : ∀[ Q ⇉ R ]) (g : ∀[ P ⇉ Q ])
        → (t : BT n k P xs) → mapBT (f ∘ g) $ t ≡ mapBT f ∘ mapBT g $ t
mapBT-∘ f g (TipZ p)  = refl
mapBT-∘ f g (TipS p)  = refl
mapBT-∘ f g (Bin t u) = cong₂ Bin (mapBT-∘ f g t) (mapBT-∘ f g u)

unTip : ∀[ BT n n P ⇉ P ]
unTip (TipS p)  = p
unTip (TipZ {xs = []} p) = p
unTip (Bin t _) = ⊥-elim (unbounded t)

unTip-natural : (h : ∀[ P ⇉ Q ]) {xs : Vec A n} (t : BT n n P xs)
                 → h ∘ unTip $ t ≡ unTip ∘ mapBT h $ t
unTip-natural h (TipS p)  = refl
unTip-natural h (TipZ {xs = []} p) = refl
unTip-natural h (Bin t _) = ⊥-elim (unbounded t)

zipBTWith : ∀[ P ⇉ Q ⇉ R ] → ∀[ BT n k P ⇉ BT n k Q ⇉ BT n k R ]
zipBTWith f (TipZ p)   (TipZ q)   = TipZ (f p q)
zipBTWith f (TipS p)   u          = TipS (f p (unTip u))
zipBTWith f (Bin t _ ) (TipS _)   = ⊥-elim (unbounded t)
zipBTWith f (Bin t t') (Bin u u') = Bin (zipBTWith f t u) (zipBTWith f t' u')

zipBTWith-natural :
    (p : ∀[ P ⇉ P' ]) (q : ∀[ Q ⇉ Q' ]) (r : ∀[ R ⇉ R' ])
    (f : ∀[ P ⇉ Q ⇉ R ]) (f' : ∀[ P' ⇉ Q' ⇉ R' ])
  → ({xs : Vec A k} {x : P xs} {y : Q xs} → r (f x y) ≡ f' (p x) (q y))
  →  {xs : Vec A n} (t : BT n k P xs) (u : BT n k Q xs)
  → mapBT r (zipBTWith f t u) ≡ zipBTWith f' (mapBT p t) (mapBT q u)
zipBTWith-natural p q r f f' f∼f' (TipZ x)   (TipZ y)   = cong TipZ f∼f'
zipBTWith-natural p q r f f' f∼f' (TipS x)   u          = cong TipS (trans f∼f' (cong (f' (p x)) (unTip-natural q u)))
zipBTWith-natural p q r f f' f∼f' (Bin t _)  (TipS _)   = ⊥-elim (unbounded t)
zipBTWith-natural p q r f f' f∼f' (Bin t t') (Bin u u') = cong₂ Bin (zipBTWith-natural p q r f f' f∼f' t u) (zipBTWith-natural p q r f f' f∼f' t' u')

blanks : (n k : ℕ) → n ≥′ k → ∀⟨ Vec A n ⟩[ BT n k (const ⊤) ]
blanks _        zero    _                      = TipZ tt
blanks (suc k) (suc k)  ≤′-refl                = TipS tt
blanks (suc n) (suc k) (≤′-step n≥1+k) {_ ∷ _} = Bin (blanks n (suc k) n≥1+k) (blanks n k n≥k)
  where n≥k = ≤′-trans (≤′-step ≤′-refl) n≥1+k

blanks↑ : (n k : ℕ) → n ≥′ k → ∀⟨ Vec A n ⟩[ const ⊤ ⇉ BT n k (const ⊤) ]
blanks↑ n k n≥k = const (blanks n k n≥k)

IsProp-≤ : {m n : ℕ} → IsProp (m ≤ n)
IsProp-≤  z≤n       z≤n       = refl
IsProp-≤ (s≤s m≤n) (s≤s m≤n') = cong s≤s (IsProp-≤ m≤n m≤n')

-- _∷ᴮᵀ_ : ∀[ P ⇉ BT (suc k) k (P ∘ (x ∷_)) ⇉ BT (suc (suc k)) (suc k) P ∘ (x ∷_) ]
_∷ᴮᵀ_ : P xs → BT (1 + k) k (P ∘ (x ∷_)) xs → BT (2 + k) (1 + k) P (x ∷ xs)
p ∷ᴮᵀ t = Bin (TipS p) t

retabulate : n > k → ∀[ BT n k P ⇉ BT n (suc k) (BT (suc k) k P) ]
retabulate 1+n>1+n       (TipS p)                       = ⊥-elim (<-irrefl refl 1+n>1+n)
retabulate _ {_ ∷ []   } (TipZ p)                       = TipS (TipZ p)
retabulate _ {_ ∷ _ ∷ _} (TipZ p)                       = Bin (retabulate 1+n>0 (TipZ p)) (TipZ (TipZ p)) where 1+n>0 = s≤s z≤n
retabulate _             (Bin t@(Bin t' _)   (TipZ q))  = Bin (retabulate 1+n>1 t) (mapBT (_∷ᴮᵀ (TipZ q)) t) where 1+n>1 = s≤s (bounded t')
retabulate _             (Bin t@(Bin _  _)   (TipS q))  = ⊥-elim (unbounded t)
retabulate _             (Bin   (TipS p)   u)           = TipS (p ∷ᴮᵀ u)
retabulate (s≤s 1+n>1+k) (Bin t@(Bin t' _) u@(Bin _ _)) = Bin (retabulate 1+n>2+k t) (zipBTWith _∷ᴮᵀ_ t (retabulate 1+n>1+k u)) where 1+n>2+k = s≤s (bounded t')

retabulate-natural : (n>k : n > k) {xs : Vec A n} (h : ∀[ P ⇉ Q ]) (t : BT n k P xs)
                   → mapBT (mapBT h) ∘ retabulate n>k $ t ≡ retabulate n>k ∘ mapBT h $ t
retabulate-natural 1+n>1+n       h (TipS p)                       = ⊥-elim (<-irrefl refl 1+n>1+n)
retabulate-natural _ {_ ∷ []   } h (TipZ p)                       = refl
retabulate-natural _ {_ ∷ _ ∷ _} h (TipZ p)                       = cong₂ Bin (retabulate-natural 1+n>0 h (TipZ p)) refl where 1+n>0 = s≤s z≤n
retabulate-natural _             h (Bin   (TipS p)   u)           = refl
retabulate-natural _             h (Bin t@(Bin t' _)   (TipZ q))  = cong₂ Bin (trans (retabulate-natural 1+n>1 h t) (cong (λ ineq → retabulate ineq (mapBT h t)) (IsProp-≤ _ _))) (trans (sym (mapBT-∘ (mapBT h) (λ p → Bin (TipS p) (TipZ q)) t)) (mapBT-∘ (λ p → Bin (TipS p) (TipZ (h q))) h t)) where 1+n>1 = s≤s (bounded t')
retabulate-natural _             h (Bin t@(Bin _  _)   (TipS q))  = ⊥-elim (unbounded t)
retabulate-natural (s≤s 1+n>1+k) h (Bin t@(Bin t' _) u@(Bin _ _)) = cong₂ Bin (trans (retabulate-natural 1+n>2+k h t) (cong (λ ineq → retabulate ineq (mapBT h t)) (IsProp-≤ _ _))) (trans (zipBTWith-natural h (mapBT h) (mapBT h) (λ p → Bin (TipS p)) (λ p → Bin (TipS p)) refl t (retabulate 1+n>1+k u)) (cong (zipBTWith (λ p → Bin (TipS p)) (mapBT h t)) (retabulate-natural 1+n>1+k h u))) where 1+n>2+k = s≤s (bounded t')

module Test where

  pattern 1+ n = suc n

  ImmediateSublistInduction : Set₁
  ImmediateSublistInduction =
    {a : Set} (s : ∀ {k} → Vec a k → Set)
    (e : {xs : Vec a 0} → ⊤ → s xs) (g : ∀ {k xs} → BT (1 + k) k s xs → s xs)
    (n : ℕ) {xs : Vec a n} → ⊤ → s xs

  td : ImmediateSublistInduction
  td s e g  0     = e
  td s e g (1+ n) = g ∘ mapBT (td s e g n) ∘ blanks↑ (1 + n) n (≤′-step ≤′-refl)

  bu : ImmediateSublistInduction
  bu s e g n = unTip ∘ loop 0 (≤⇒≤‴ z≤n) ∘ mapBT e ∘ blanks↑ n 0 (≤⇒≤′ z≤n)
    where
      loop : (k : ℕ) → k ≤‴ n → BT n k s xs → BT n n s xs
      loop n  ≤‴-refl        = id
      loop k (≤‴-step n≥1+k) = loop (1 + k) n≥1+k ∘ mapBT g ∘ retabulate (≤‴⇒≤ n≥1+k)

module Algorithms
  {A : Set} (S : {k : ℕ} → Vec A k → Set)
  (e : S []) (g : {k : ℕ} → ∀[ BT (suc k) k S ⇉ S ])
  -- (e : S []) (g : {k : ℕ} {xs : Vec A (suc k)} → BT (suc k) k S xs → S xs)
  -- (e : S) (g : List S → S)
  where

  e↑ : ∀⟨ Vec A 0 ⟩[ const ⊤ ⇉ S ]
  e↑ {[]} = const e

  td : (n : ℕ) → ∀⟨ Vec A n ⟩[ const ⊤ ⇉ S ]
  td  zero   = e↑
  td (suc n) = g ∘ mapBT (td n) ∘ blanks↑ (suc n) n 1+n≥n
    where 1+n≥n = ≤′-step ≤′-refl

  bu-loop : n ≥‴ k → ∀[ BT n k S ⇉ BT n n S ]
  bu-loop  ≤‴-refl        = id
  bu-loop (≤‴-step n≥1+k) = bu-loop n≥1+k ∘ mapBT g ∘ retabulate (≤‴⇒≤ n≥1+k)

  bu : (n : ℕ) → ∀⟨ Vec A n ⟩[ const ⊤ ⇉ S ]
  bu n = unTip ∘ bu-loop (≤⇒≤‴ z≤n) ∘ mapBT e↑ ∘ blanks↑ n 0 (≤⇒≤′ z≤n)
  -- bu _ = unTip (bu-loop (≤⇒≤‴ z≤n) (TipZ e))


--------
-- Correctness: separating both algorithms into production and consumption phases

module Production where

  tdRec : (n : ℕ) → Vec A n → Set
  tdRec  zero   = const ⊤
  tdRec (suc n) = BT (suc n) n (tdRec n)

  td-produce : (n : ℕ) → ∀⟨ Vec A n ⟩[ const ⊤ ⇉ tdRec n ]
  td-produce  zero   = id
  td-produce (suc n) = mapBT (td-produce n) ∘ blanks↑ (suc n) n 1+n≥n
    where 1+n≥n = ≤′-step ≤′-refl

  IsProp-tdRec : (n : ℕ) {xs : Vec A n} → IsProp (tdRec n xs)
  IsProp-tdRec  zero   = λ _ _ → refl
  IsProp-tdRec (suc n) = IsProp-BT (IsProp-tdRec n)

  buRec : n ≥‴ k → (Vec A k → Set) → Vec A n → Set
  buRec          ≤‴-refl        = id
  buRec {k = k} (≤‴-step n≥1+k) = buRec n≥1+k ∘ BT (suc k) k

  bu-produce-loop : (n≥k : n ≥‴ k) → ∀[ BT n k P ⇉ BT n n (buRec n≥k P) ]
  bu-produce-loop  ≤‴-refl        = id
  bu-produce-loop (≤‴-step n≥1+k) = bu-produce-loop n≥1+k ∘ retabulate (≤‴⇒≤ n≥1+k)

  bu-produce : (n : ℕ) → ∀⟨ Vec A n ⟩[ const ⊤ ⇉ buRec (≤⇒≤‴ z≤n) (const ⊤) ]
  bu-produce n = unTip ∘ bu-produce-loop (≤⇒≤‴ z≤n) ∘ blanks↑ n 0 (≤⇒≤′ z≤n)

  map-buRec : (n≥k : n ≥‴ k) → ∀[ P ⇉ Q ] → ∀[ buRec n≥k P ⇉ buRec n≥k Q ]
  map-buRec  ≤‴-refl        f = f
  map-buRec (≤‴-step n≥1+k) f = map-buRec n≥1+k (mapBT f)

  cong-map-buRec :
      (n≥k : n ≥‴ k) {f g : ∀[ P ⇉ Q ]} → (∀ {ys} (p : P ys) → f p ≡ g p)
    → {xs : Vec A n} (t : buRec n≥k P xs) → map-buRec n≥k f t ≡ map-buRec n≥k g t
  cong-map-buRec  ≤‴-refl        f≗g t = f≗g t
  cong-map-buRec (≤‴-step n≥1+k) f≗g t = cong-map-buRec n≥1+k (cong-mapBT f≗g) t

  map-buRec-∘ : (n≥k : n ≥‴ k) (f : ∀[ Q ⇉ R ]) (g : ∀[ P ⇉ Q ])
              → {xs : Vec A n} (t : buRec n≥k P xs)
              → map-buRec n≥k (f ∘ g) $ t ≡ map-buRec n≥k f ∘ map-buRec n≥k g $ t
  map-buRec-∘  ≤‴-refl        f g t = refl
  map-buRec-∘ (≤‴-step n≥1+k) f g t =
    trans (cong-map-buRec n≥1+k (mapBT-∘ f g) t) (map-buRec-∘ n≥1+k (mapBT f) (mapBT g) t)

  bu-produce-loop-natural :
      (n≥k : n ≥‴ k) (h : ∀[ P ⇉ Q ]) {xs : Vec A n} (t : BT n k P xs)
    → mapBT (map-buRec n≥k h) ∘ bu-produce-loop n≥k $ t ≡ bu-produce-loop n≥k ∘ mapBT h $ t
  bu-produce-loop-natural  ≤‴-refl        h t = refl
  bu-produce-loop-natural (≤‴-step n≥1+k) h t =
    begin
      mapBT (map-buRec (≤‴-step n≥1+k) h) ∘ bu-produce-loop (≤‴-step n≥1+k)               $ t
        ≡⟨ refl ⟩
      mapBT (map-buRec n≥1+k (mapBT h)) ∘ bu-produce-loop n≥1+k ∘ retabulate (≤‴⇒≤ n≥1+k) $ t
        ≡⟨ bu-produce-loop-natural n≥1+k (mapBT h) _ ⟩
      bu-produce-loop n≥1+k ∘ mapBT (mapBT h) ∘ retabulate (≤‴⇒≤ n≥1+k)                   $ t
        ≡⟨ cong (bu-produce-loop n≥1+k) (retabulate-natural (≤‴⇒≤ n≥1+k) h t) ⟩
      bu-produce-loop n≥1+k ∘ retabulate (≤‴⇒≤ n≥1+k) ∘ mapBT h                           $ t
        ≡⟨ refl ⟩
      bu-produce-loop (≤‴-step n≥1+k) ∘ mapBT h                                           $ t
    ∎
    where open ≡-Reasoning

  unTip∘bu-produce-loop-natural :
      (n≥k : n ≥‴ k) (h : ∀[ P ⇉ Q ]) {xs : Vec A n} (t : BT n k P xs)
    → map-buRec n≥k h ∘ unTip ∘ bu-produce-loop n≥k           $ t
    ≡                   unTip ∘ bu-produce-loop n≥k ∘ mapBT h $ t
  unTip∘bu-produce-loop-natural n≥k h t =
      begin
        map-buRec n≥k h ∘ unTip ∘ bu-produce-loop n≥k         $ t
          ≡⟨ unTip-natural (map-buRec n≥k h) (bu-produce-loop n≥k t) ⟩
        unTip ∘ mapBT (map-buRec n≥k h) ∘ bu-produce-loop n≥k $ t
          ≡⟨ cong unTip (bu-produce-loop-natural n≥k h _) ⟩
        unTip ∘ bu-produce-loop n≥k ∘ mapBT h                 $ t
      ∎
    where open ≡-Reasoning

  overall : {A A' B : Set}
          → (f : A → B) (f' : A' → B)
          → ((Σ[ X ∈ Set ] (X → B)) ∋ (A , f)) ≡ (A' , f')
          → IsProp A
          → (a : A) (a' : A') → f a ≡ f' a'
  overall f .f refl IsProp-A a a' = cong f (IsProp-A a a')

module Consumption-and-Correctness
  {A : Set} (S : {k : ℕ} → Vec A k → Set)
  (e : S []) (g : {k : ℕ} → ∀[ BT (suc k) k S ⇉ S ])
  where

  open Algorithms S e g
  open Production

  td-consume : (n : ℕ) → ∀[ tdRec n ⇉ S ]
  td-consume  zero   = e↑
  td-consume (suc n) = g ∘ mapBT (td-consume n)

  td-separation : (n : ℕ) {xs : Vec A n}
                → td n {xs} $ tt ≡ td-consume n ∘ td-produce n $ tt
  td-separation  zero   = refl
  td-separation (suc n) =
    begin
      td (suc n)                                                                $ tt
        ≡⟨ refl ⟩
      g ∘ mapBT (td n) ∘ blanks↑ (suc n) n 1+n≥n                                $ tt
        ≡⟨ cong g (cong-mapBT (λ _ → td-separation n) _) ⟩
      g ∘ mapBT (td-consume n ∘ td-produce n) ∘ blanks↑ (suc n) n 1+n≥n         $ tt
        ≡⟨ cong g (mapBT-∘ (td-consume n) (td-produce n) _) ⟩
      g ∘ mapBT (td-consume n) ∘ mapBT (td-produce n) ∘ blanks↑ (suc n) n 1+n≥n $ tt
        ≡⟨ refl ⟩
      td-consume (suc n) ∘ td-produce (suc n)                                   $ tt
    ∎
    where 1+n≥n = ≤′-step ≤′-refl
          open ≡-Reasoning

  bu-consume-loop : (n≥k : n ≥‴ k) → ∀[ buRec n≥k S ⇉ S ]
  bu-consume-loop  ≤‴-refl        = id
  bu-consume-loop (≤‴-step n≥1+k) = bu-consume-loop n≥1+k ∘ map-buRec n≥1+k g

  bu-consume : (n : ℕ) → ∀⟨ Vec A n ⟩[ buRec (≤⇒≤‴ z≤n) (const ⊤) ⇉ S ]
  bu-consume n = bu-consume-loop n≥0 ∘ map-buRec n≥0 e↑
    where n≥0 = ≤⇒≤‴ z≤n

  bu-loop-separation :
      (n≥k : n ≥‴ k)
    → {xs : Vec A n} (t : BT n k S xs)
    → unTip ∘ bu-loop n≥k $ t ≡ bu-consume-loop n≥k ∘ unTip ∘ bu-produce-loop n≥k $ t
  bu-loop-separation  ≤‴-refl        t = refl
  bu-loop-separation (≤‴-step n≥1+k) t =
    begin
      unTip ∘ bu-loop (≤‴-step n≥1+k)                                                                     $ t
        ≡⟨ refl ⟩
      unTip ∘ bu-loop n≥1+k ∘ mapBT g ∘ retabulate (≤‴⇒≤ n≥1+k)                                           $ t
        ≡⟨ bu-loop-separation n≥1+k _ ⟩
      bu-consume-loop n≥1+k ∘ unTip ∘ bu-produce-loop n≥1+k ∘ mapBT g ∘ retabulate (≤‴⇒≤ n≥1+k)           $ t
        ≡⟨ cong (bu-consume-loop n≥1+k) (sym (unTip∘bu-produce-loop-natural n≥1+k g _)) ⟩
      bu-consume-loop n≥1+k ∘ map-buRec n≥1+k g ∘ unTip ∘ bu-produce-loop n≥1+k ∘ retabulate (≤‴⇒≤ n≥1+k) $ t
        ≡⟨ refl ⟩
      bu-consume-loop (≤‴-step n≥1+k) ∘ unTip ∘ bu-produce-loop (≤‴-step n≥1+k)                           $ t
    ∎
    where open ≡-Reasoning

  bu-separation : (n : ℕ) {xs : Vec A n} → bu n {xs} $ tt ≡ bu-consume n ∘ bu-produce n $ tt
  bu-separation n =
    begin
      bu n                                                                                          $ tt
        ≡⟨ refl ⟩
      unTip ∘ bu-loop n≥0 ∘ mapBT e↑ ∘ blanks↑ n 0 (≤⇒≤′ z≤n)                                       $ tt
        ≡⟨ bu-loop-separation n≥0 _ ⟩
      bu-consume-loop n≥0 ∘ unTip ∘ bu-produce-loop n≥0 ∘ mapBT e↑ ∘ blanks↑ n 0 (≤⇒≤′ z≤n)         $ tt
        ≡⟨ cong (bu-consume-loop n≥0) (sym (unTip∘bu-produce-loop-natural n≥0 e↑ _)) ⟩
      bu-consume-loop n≥0 ∘ map-buRec n≥0 e↑ ∘ unTip ∘ bu-produce-loop n≥0 ∘ blanks↑ n 0 (≤⇒≤′ z≤n) $ tt
        ≡⟨ refl ⟩
      bu-consume n ∘ bu-produce n                                                                   $ tt
    ∎
    where n≥0 = ≤⇒≤‴ z≤n
          open ≡-Reasoning

  bu-consume-loop' : (n≥k : n ≥‴ k) → ∀[ R ⇉ S ] → ∀[ buRec n≥k R ⇉ S ]
  bu-consume-loop'  ≤‴-refl        h = h
  bu-consume-loop' (≤‴-step n≥1+k) h = bu-consume-loop' n≥1+k (g ∘ mapBT h)

  bu-consume' : (n : ℕ) → ∀⟨ Vec A n ⟩[ buRec (≤⇒≤‴ z≤n) (const ⊤) ⇉ S ]
  bu-consume' n = bu-consume-loop' (≤⇒≤‴ z≤n) e↑

  bu-consume-loop-equiv :
      (n≥k : n ≥‴ k) (h : ∀[ R ⇉ S ]) {xs : Vec A n} (r : buRec n≥k R xs)
    → bu-consume-loop' n≥k h $ r ≡ bu-consume-loop n≥k ∘ map-buRec n≥k h $ r
  bu-consume-loop-equiv  ≤‴-refl        h r = refl
  bu-consume-loop-equiv (≤‴-step n≥1+k) h r =
    begin
      bu-consume-loop' (≤‴-step n≥1+k) h                                    $ r
        ≡⟨ refl ⟩
      bu-consume-loop' n≥1+k (g ∘ mapBT h)                                  $ r
        ≡⟨ bu-consume-loop-equiv n≥1+k (g ∘ mapBT h) _ ⟩
      bu-consume-loop n≥1+k ∘ map-buRec n≥1+k (g ∘ mapBT h)                 $ r
        ≡⟨ cong (bu-consume-loop n≥1+k) (map-buRec-∘ n≥1+k g (mapBT h) _) ⟩
      bu-consume-loop n≥1+k ∘ map-buRec n≥1+k g ∘ map-buRec n≥1+k (mapBT h) $ r
        ≡⟨ refl ⟩
      bu-consume-loop (≤‴-step n≥1+k) ∘ map-buRec (≤‴-step n≥1+k) h         $ r
    ∎
    where open ≡-Reasoning

  bu-consume-equiv :
      (n : ℕ) {xs : Vec A n} (r : buRec (≤⇒≤‴ z≤n) (const ⊤) xs)
    → bu-consume' n r ≡ bu-consume n r
  bu-consume-equiv n = bu-consume-loop-equiv (≤⇒≤‴ z≤n) e↑

  td≗bu-consume :
      (n≥k : n ≥‴ k) {xs : Vec A n}
    → ((Σ[ X ∈ Set ] (X → S xs))
      ∋ (tdRec n xs             , td-consume n))
      ≡ (buRec n≥k (tdRec k) xs , bu-consume-loop' n≥k (td-consume k))
  td≗bu-consume  ≤‴-refl        = refl
  td≗bu-consume (≤‴-step n≥1+k) = td≗bu-consume n≥1+k

  td≗bu : (n : ℕ) {xs : Vec A n} → td n {xs} $ tt ≡ bu n $ tt
  td≗bu n =
    begin
      td n                         $ tt
        ≡⟨ td-separation n ⟩
      td-consume n ∘ td-produce n  $ tt
        ≡⟨ overall (td-consume n) (bu-consume-loop' n≥0 e↑) (td≗bu-consume n≥0)
             (IsProp-tdRec n) (td-produce n tt) (bu-produce n tt) ⟩
      bu-consume' n ∘ bu-produce n $ tt
        ≡⟨ bu-consume-equiv n _ ⟩
      bu-consume n ∘ bu-produce n  $ tt
        ≡⟨ sym (bu-separation n) ⟩
      bu n                         $ tt
    ∎
    where n≥0 = ≤⇒≤‴ z≤n
          open ≡-Reasoning

IsProp' : Set → Set
IsProp' a = {x y : a} → x ≡ y

IsProp'-BT : ({ys : Vec A k} → IsProp' (P ys))
           →  {xs : Vec A n} → IsProp' (BT n k P xs)
IsProp'-BT isProp'-P = IsProp-BT (λ _ _ → isProp'-P) _ _

retabulate-blanks :
  ∀ {n>k n≥k 1+k≥k n≥1+k}
  → retabulate n>k (blanks↑ n k n≥k {xs} tt)
  ≡ mapBT (blanks↑ (1 + k) k 1+k≥k) (blanks↑ n (1 + k) n≥1+k tt)
retabulate-blanks = IsProp'-BT (IsProp'-BT refl)

