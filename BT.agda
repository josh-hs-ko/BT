{-# OPTIONS --safe --large-indices --no-forced-argument-recursion #-}

module BT where

open import Function renaming (_$_ to infixr 5 _$_)
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec
open import Relation.Binary.PropositionalEquality

variable
  A B C          : Set
  k m n          : ℕ
  x              : A
  xs ys          : Vec A _
  P P' Q Q' R R' : A → Set


--------
-- Notations for understanding indexed types as if they were simple types
-- Or: switching to the categories of families

Fam : Set → Set₁
Fam A = A → Set

_⇉_ : Fam A → Fam A → Set
P ⇉ Q = ∀ {x} → P x → Q x

infix 2 _⇉_

_⇒_ : Fam A → Fam A → Fam A
(P ⇒ Q) x = P x → Q x

infixr 3 _⇒_

∀[_]_⇉_ : (A : Set) → Fam A → Fam A → Set
∀[ A ] P ⇉ Q = P ⇉ Q

infix 2 ∀[_]_⇉_

--------
-- Binomial trees

data BT : (n k : ℕ) → Fam (Vec A k) → Fam (Vec A n) where
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
IsProp A = {x y : A} → x ≡ y

IsProp' : Set → Set
IsProp' A = (x y : A) → x ≡ y

BT-isProp' : (∀ {ys} → IsProp (P ys)) → IsProp' (BT n k P xs)
BT-isProp' P-isProp (TipZ p)  (TipZ p')   = cong TipZ P-isProp
BT-isProp' P-isProp (TipS p)  (TipS p')   = cong TipS P-isProp
BT-isProp' P-isProp (Bin t u) (Bin t' u') = cong₂ Bin (BT-isProp' P-isProp t t')
                                                      (BT-isProp' P-isProp u u')
BT-isProp' P-isProp (TipS p)  (Bin t' _)  = ⊥-elim (unbounded t')
BT-isProp' P-isProp (Bin t u) (TipS p')   = ⊥-elim (unbounded t)

BT-isProp : (∀ {ys} → IsProp (P ys)) → IsProp (BT n k P xs)
BT-isProp P-isProp = BT-isProp' P-isProp _ _

-- mapBT : (∀ {xs} → P xs → Q xs) → ∀ {xs} → BT n k P xs → BT n k Q xs
mapBT : (P ⇉ Q) → BT n k P ⇉ BT n k Q
mapBT f (TipZ p)  = TipZ (f p)
mapBT f (TipS p)  = TipS (f p)
mapBT f (Bin t u) = Bin (mapBT f t) (mapBT f u)

cong-mapBT : {f g : P ⇉ Q} → (∀ {ys} (p : P ys) → f p ≡ g p)
           → (t : BT n k P xs) → mapBT f t ≡ mapBT g t
cong-mapBT f≗g (TipZ p)  = cong TipZ (f≗g p)
cong-mapBT f≗g (TipS p)  = cong TipS (f≗g p)
cong-mapBT f≗g (Bin t u) = cong₂ Bin (cong-mapBT f≗g t) (cong-mapBT f≗g u)

mapBT-∘ : (f : Q ⇉ R) (g : P ⇉ Q)
        → (t : BT n k P xs) → mapBT (f ∘ g) $ t ≡ mapBT f ∘ mapBT g $ t
mapBT-∘ f g (TipZ p)  = refl
mapBT-∘ f g (TipS p)  = refl
mapBT-∘ f g (Bin t u) = cong₂ Bin (mapBT-∘ f g t) (mapBT-∘ f g u)

unTip : BT n n P ⇉ P
unTip (TipS p)  = p
unTip (TipZ {xs = []} p) = p
unTip (Bin t _) = ⊥-elim (unbounded t)

unTip-natural : (h : P ⇉ Q) {xs : Vec A n} (t : BT n n P xs)
              → h ∘ unTip $ t ≡ unTip ∘ mapBT h $ t
unTip-natural h (TipS p)  = refl
unTip-natural h (TipZ {xs = []} p) = refl
unTip-natural h (Bin t _) = ⊥-elim (unbounded t)

zipBTWith : (P ⇉ Q ⇒ R) → (BT n k P ⇉ BT n k Q ⇒ BT n k R)
zipBTWith f (TipZ p)   (TipZ q)   = TipZ (f p q)
zipBTWith f (TipS p)   u          = TipS (f p (unTip u))
zipBTWith f (Bin t _ ) (TipS _)   = ⊥-elim (unbounded t)
zipBTWith f (Bin t t') (Bin u u') = Bin (zipBTWith f t u) (zipBTWith f t' u')

zipBTWith-natural :
    (p : P ⇉ P') (q : Q ⇉ Q') (r : R ⇉ R')
    (f : P ⇉ Q ⇒ R) (f' : P' ⇉ Q' ⇒ R')
  → ({xs : Vec A k} {x : P xs} {y : Q xs} → r (f x y) ≡ f' (p x) (q y))
  →  {xs : Vec A n} (t : BT n k P xs) (u : BT n k Q xs)
  → mapBT r (zipBTWith f t u) ≡ zipBTWith f' (mapBT p t) (mapBT q u)
zipBTWith-natural p q r f f' f∼f' (TipZ x)   (TipZ y)   = cong TipZ f∼f'
zipBTWith-natural p q r f f' f∼f' (TipS x)   u          = cong TipS (trans f∼f' (cong (f' (p x)) (unTip-natural q u)))
zipBTWith-natural p q r f f' f∼f' (Bin t _)  (TipS _)   = ⊥-elim (unbounded t)
zipBTWith-natural p q r f f' f∼f' (Bin t t') (Bin u u') = cong₂ Bin (zipBTWith-natural p q r f f' f∼f' t u) (zipBTWith-natural p q r f f' f∼f' t' u')

blanks' : (n k : ℕ) → n ≥′ k → {xs : Vec A n} → BT n k (const ⊤) xs
blanks' _        zero   _                       = TipZ tt
blanks' (suc k) (suc k)  ≤′-refl                = TipS tt
blanks' (suc n) (suc k) (≤′-step n≥1+k) {_ ∷ _} = Bin (blanks' n (suc k) n≥1+k) (blanks' n k n≥k)
  where n≥k = ≤′-trans (≤′-step ≤′-refl) n≥1+k

blanks : (n k : ℕ) → n ≥′ k → ∀[ Vec A n ] const ⊤ ⇉ BT n k (const ⊤)
blanks n k n≥k = const (blanks' n k n≥k)

≤-isProp' : {m n : ℕ} → IsProp' (m ≤ n)
≤-isProp'  z≤n       z≤n       = refl
≤-isProp' (s≤s m≤n) (s≤s m≤n') = cong s≤s (≤-isProp' m≤n m≤n')

≤-isProp : {m n : ℕ} → IsProp (m ≤ n)
≤-isProp = ≤-isProp' _ _

_∷ᴮᵀ_ : P xs → BT (1 + k) k (P ∘ (x ∷_)) xs → BT (2 + k) (1 + k) P (x ∷ xs)
p ∷ᴮᵀ t = Bin (TipS p) t

retabulate : n > k → BT n k P ⇉ BT n (suc k) (BT (suc k) k P)
retabulate 1+n>1+n       (TipS p)                       = ⊥-elim (<-irrefl refl 1+n>1+n)
retabulate _ {_ ∷ []   } (TipZ p)                       = TipS (TipZ p)
retabulate _ {_ ∷ _ ∷ _} (TipZ p)                       = Bin (retabulate 1+n>0 (TipZ p)) (TipZ (TipZ p)) where 1+n>0 = s≤s z≤n
retabulate _             (Bin t@(Bin t' _)   (TipZ q))  = Bin (retabulate 1+n>1 t) (mapBT (_∷ᴮᵀ (TipZ q)) t) where 1+n>1 = s≤s (bounded t')
retabulate _             (Bin t@(Bin _  _)   (TipS q))  = ⊥-elim (unbounded t)
retabulate _             (Bin   (TipS p)   u)           = TipS (p ∷ᴮᵀ u)
retabulate (s≤s 1+n>1+k) (Bin t@(Bin t' _) u@(Bin _ _)) = Bin (retabulate 1+n>2+k t) (zipBTWith _∷ᴮᵀ_ t (retabulate 1+n>1+k u)) where 1+n>2+k = s≤s (bounded t')

retabulate-natural : (n>k : n > k) {xs : Vec A n} (h : P ⇉ Q) (t : BT n k P xs)
                   → mapBT (mapBT h) ∘ retabulate n>k $ t ≡ retabulate n>k ∘ mapBT h $ t
retabulate-natural 1+n>1+n       h (TipS p)                       = ⊥-elim (<-irrefl refl 1+n>1+n)
retabulate-natural _ {_ ∷ []   } h (TipZ p)                       = refl
retabulate-natural _ {_ ∷ _ ∷ _} h (TipZ p)                       = cong₂ Bin (retabulate-natural 1+n>0 h (TipZ p)) refl where 1+n>0 = s≤s z≤n
retabulate-natural _             h (Bin   (TipS p)   u)           = refl
retabulate-natural _             h (Bin t@(Bin t' _)   (TipZ q))  = cong₂ Bin (trans (retabulate-natural 1+n>1 h t) (cong (λ ineq → retabulate ineq (mapBT h t)) ≤-isProp)) (trans (sym (mapBT-∘ (mapBT h) (λ p → Bin (TipS p) (TipZ q)) t)) (mapBT-∘ (λ p → Bin (TipS p) (TipZ (h q))) h t)) where 1+n>1 = s≤s (bounded t')
retabulate-natural _             h (Bin t@(Bin _  _)   (TipS q))  = ⊥-elim (unbounded t)
retabulate-natural (s≤s 1+n>1+k) h (Bin t@(Bin t' _) u@(Bin _ _)) = cong₂ Bin (trans (retabulate-natural 1+n>2+k h t) (cong (λ ineq → retabulate ineq (mapBT h t)) ≤-isProp)) (trans (zipBTWith-natural h (mapBT h) (mapBT h) (λ p → Bin (TipS p)) (λ p → Bin (TipS p)) refl t (retabulate 1+n>1+k u)) (cong (zipBTWith (λ p → Bin (TipS p)) (mapBT h t)) (retabulate-natural 1+n>1+k h u))) where 1+n>2+k = s≤s (bounded t')

module Algorithms
  {A : Set} (S : {k : ℕ} → Fam (Vec A k))
  (e : ∀[ Vec A 0 ] const ⊤ ⇉ S) (g : {k : ℕ} → BT (suc k) k S ⇉ S)
  where

  td : (n : ℕ) → ∀[ Vec A n ] const ⊤ ⇉ S
  td  zero   = e
  td (suc n) = g ∘ mapBT (td n) ∘ blanks (suc n) n 1+n≥n
    where 1+n≥n = ≤′-step ≤′-refl

  bu-loop : n ≥‴ k → BT n k S ⇉ BT n n S
  bu-loop  ≤‴-refl        = id
  bu-loop (≤‴-step n≥1+k) = bu-loop n≥1+k ∘ mapBT g ∘ retabulate (≤‴⇒≤ n≥1+k)

  bu : (n : ℕ) → ∀[ Vec A n ] const ⊤ ⇉ S
  bu n = unTip ∘ bu-loop (≤⇒≤‴ z≤n) ∘ mapBT e ∘ blanks n 0 (≤⇒≤′ z≤n)
  -- bu _ = unTip (bu-loop (≤⇒≤‴ z≤n) (TipZ e))


--------
-- Correctness: separating both algorithms into production and consumption phases

module Production where

  tdRec : (n : ℕ) → Fam (Vec A n)
  tdRec  zero   = const ⊤
  tdRec (suc n) = BT (suc n) n (tdRec n)

  td-construct : (n : ℕ) → ∀[ Vec A n ] const ⊤ ⇉ tdRec n
  td-construct  zero   = id
  td-construct (suc n) = mapBT (td-construct n) ∘ blanks (suc n) n 1+n≥n
    where 1+n≥n = ≤′-step ≤′-refl

  tdRec-isProp : (n : ℕ) {xs : Vec A n} → IsProp (tdRec n xs)
  tdRec-isProp  zero   = refl
  tdRec-isProp (suc n) = BT-isProp (tdRec-isProp n)

  buRec : n ≥‴ k → Fam (Vec A k) → Fam (Vec A n)
  buRec          ≤‴-refl        = id
  buRec {k = k} (≤‴-step n≥1+k) = buRec n≥1+k ∘ BT (suc k) k

  bu-construct-loop : (n≥k : n ≥‴ k) → BT n k P ⇉ BT n n (buRec n≥k P)
  bu-construct-loop  ≤‴-refl        = id
  bu-construct-loop (≤‴-step n≥1+k) = bu-construct-loop n≥1+k ∘ retabulate (≤‴⇒≤ n≥1+k)

  bu-construct : (n : ℕ) → ∀[ Vec A n ] const ⊤ ⇉ buRec (≤⇒≤‴ z≤n) (const ⊤)
  bu-construct n = unTip ∘ bu-construct-loop (≤⇒≤‴ z≤n) ∘ blanks n 0 (≤⇒≤′ z≤n)

  map-buRec : (n≥k : n ≥‴ k) → P ⇉ Q → buRec n≥k P ⇉ buRec n≥k Q
  map-buRec  ≤‴-refl        f = f
  map-buRec (≤‴-step n≥1+k) f = map-buRec n≥1+k (mapBT f)

  cong-map-buRec :
      (n≥k : n ≥‴ k) {f g : P ⇉ Q} → (∀ {ys} (p : P ys) → f p ≡ g p)
    → {xs : Vec A n} (t : buRec n≥k P xs) → map-buRec n≥k f t ≡ map-buRec n≥k g t
  cong-map-buRec  ≤‴-refl        f≗g t = f≗g t
  cong-map-buRec (≤‴-step n≥1+k) f≗g t = cong-map-buRec n≥1+k (cong-mapBT f≗g) t

  map-buRec-∘ : (n≥k : n ≥‴ k) (f : Q ⇉ R) (g : P ⇉ Q)
              → {xs : Vec A n} (t : buRec n≥k P xs)
              → map-buRec n≥k (f ∘ g) $ t ≡ map-buRec n≥k f ∘ map-buRec n≥k g $ t
  map-buRec-∘  ≤‴-refl        f g t = refl
  map-buRec-∘ (≤‴-step n≥1+k) f g t =
    trans (cong-map-buRec n≥1+k (mapBT-∘ f g) t) (map-buRec-∘ n≥1+k (mapBT f) (mapBT g) t)

  bu-construct-loop-natural :
      (n≥k : n ≥‴ k) (h : P ⇉ Q) {xs : Vec A n} (t : BT n k P xs)
    → mapBT (map-buRec n≥k h) ∘ bu-construct-loop n≥k $ t ≡ bu-construct-loop n≥k ∘ mapBT h $ t
  bu-construct-loop-natural  ≤‴-refl        h t = refl
  bu-construct-loop-natural (≤‴-step n≥1+k) h t =
    begin
      mapBT (map-buRec (≤‴-step n≥1+k) h) ∘ bu-construct-loop (≤‴-step n≥1+k)               $ t
        ≡⟨ refl ⟩
      mapBT (map-buRec n≥1+k (mapBT h)) ∘ bu-construct-loop n≥1+k ∘ retabulate (≤‴⇒≤ n≥1+k) $ t
        ≡⟨ bu-construct-loop-natural n≥1+k (mapBT h) _ ⟩
      bu-construct-loop n≥1+k ∘ mapBT (mapBT h) ∘ retabulate (≤‴⇒≤ n≥1+k)                   $ t
        ≡⟨ cong (bu-construct-loop n≥1+k) (retabulate-natural (≤‴⇒≤ n≥1+k) h t) ⟩
      bu-construct-loop n≥1+k ∘ retabulate (≤‴⇒≤ n≥1+k) ∘ mapBT h                           $ t
        ≡⟨ refl ⟩
      bu-construct-loop (≤‴-step n≥1+k) ∘ mapBT h                                           $ t
    ∎
    where open ≡-Reasoning

  unTip∘bu-construct-loop-natural :
      (n≥k : n ≥‴ k) (h : P ⇉ Q) {xs : Vec A n} (t : BT n k P xs)
    → map-buRec n≥k h ∘ unTip ∘ bu-construct-loop n≥k           $ t
    ≡                   unTip ∘ bu-construct-loop n≥k ∘ mapBT h $ t
  unTip∘bu-construct-loop-natural n≥k h t =
      begin
        map-buRec n≥k h ∘ unTip ∘ bu-construct-loop n≥k         $ t
          ≡⟨ unTip-natural (map-buRec n≥k h) (bu-construct-loop n≥k t) ⟩
        unTip ∘ mapBT (map-buRec n≥k h) ∘ bu-construct-loop n≥k $ t
          ≡⟨ cong unTip (bu-construct-loop-natural n≥k h _) ⟩
        unTip ∘ bu-construct-loop n≥k ∘ mapBT h                 $ t
      ∎
    where open ≡-Reasoning

  overall : {A A' B : Set}
          → (f : A → B) (f' : A' → B)
          → ((Σ[ X ∈ Set ] (X → B)) ∋ (A , f)) ≡ (A' , f')
          → IsProp A
          → (a : A) (a' : A') → f a ≡ f' a'
  overall f .f refl A-isProp a a' = cong f A-isProp

module Consumption-and-Correctness
  {A : Set} (S : {k : ℕ} → Fam (Vec A k))
  (e : ∀[ Vec A 0 ] const ⊤ ⇉ S) (g : {k : ℕ} → BT (suc k) k S ⇉ S)
  where

  open Algorithms S e g
  open Production

  td-demolish : (n : ℕ) → tdRec n ⇉ S
  td-demolish  zero   = e
  td-demolish (suc n) = g ∘ mapBT (td-demolish n)

  td-separation : (n : ℕ) {xs : Vec A n}
                → td n {xs} $ tt ≡ td-demolish n ∘ td-construct n $ tt
  td-separation  zero   = refl
  td-separation (suc n) =
    begin
      td (suc n)                                                                  $ tt
        ≡⟨ refl ⟩
      g ∘ mapBT (td n) ∘ blanks (suc n) n 1+n≥n                                   $ tt
        ≡⟨ cong g (cong-mapBT (λ _ → td-separation n) _) ⟩
      g ∘ mapBT (td-demolish n ∘ td-construct n) ∘ blanks (suc n) n 1+n≥n         $ tt
        ≡⟨ cong g (mapBT-∘ (td-demolish n) (td-construct n) _) ⟩
      g ∘ mapBT (td-demolish n) ∘ mapBT (td-construct n) ∘ blanks (suc n) n 1+n≥n $ tt
        ≡⟨ refl ⟩
      td-demolish (suc n) ∘ td-construct (suc n)                                  $ tt
    ∎
    where 1+n≥n = ≤′-step ≤′-refl
          open ≡-Reasoning

  bu-demolish-loop : (n≥k : n ≥‴ k) → buRec n≥k S ⇉ S
  bu-demolish-loop  ≤‴-refl        = id
  bu-demolish-loop (≤‴-step n≥1+k) = bu-demolish-loop n≥1+k ∘ map-buRec n≥1+k g

  bu-demolish : (n : ℕ) → ∀[ Vec A n ] buRec (≤⇒≤‴ z≤n) (const ⊤) ⇉ S
  bu-demolish n = bu-demolish-loop n≥0 ∘ map-buRec n≥0 e
    where n≥0 = ≤⇒≤‴ z≤n

  bu-loop-separation :
      (n≥k : n ≥‴ k)
    → {xs : Vec A n} (t : BT n k S xs)
    → unTip ∘ bu-loop n≥k $ t ≡ bu-demolish-loop n≥k ∘ unTip ∘ bu-construct-loop n≥k $ t
  bu-loop-separation  ≤‴-refl        t = refl
  bu-loop-separation (≤‴-step n≥1+k) t =
    begin
      unTip ∘ bu-loop (≤‴-step n≥1+k)                                                                        $ t
        ≡⟨ refl ⟩
      unTip ∘ bu-loop n≥1+k ∘ mapBT g ∘ retabulate (≤‴⇒≤ n≥1+k)                                              $ t
        ≡⟨ bu-loop-separation n≥1+k _ ⟩
      bu-demolish-loop n≥1+k ∘ unTip ∘ bu-construct-loop n≥1+k ∘ mapBT g ∘ retabulate (≤‴⇒≤ n≥1+k)           $ t
        ≡⟨ cong (bu-demolish-loop n≥1+k) (sym (unTip∘bu-construct-loop-natural n≥1+k g _)) ⟩
      bu-demolish-loop n≥1+k ∘ map-buRec n≥1+k g ∘ unTip ∘ bu-construct-loop n≥1+k ∘ retabulate (≤‴⇒≤ n≥1+k) $ t
        ≡⟨ refl ⟩
      bu-demolish-loop (≤‴-step n≥1+k) ∘ unTip ∘ bu-construct-loop (≤‴-step n≥1+k)                           $ t
    ∎
    where open ≡-Reasoning

  bu-separation : (n : ℕ) {xs : Vec A n} → bu n {xs} $ tt ≡ bu-demolish n ∘ bu-construct n $ tt
  bu-separation n =
    begin
      bu n                                                                                           $ tt
        ≡⟨ refl ⟩
      unTip ∘ bu-loop n≥0 ∘ mapBT e ∘ blanks n 0 (≤⇒≤′ z≤n)                                          $ tt
        ≡⟨ bu-loop-separation n≥0 _ ⟩
      bu-demolish-loop n≥0 ∘ unTip ∘ bu-construct-loop n≥0 ∘ mapBT e ∘ blanks n 0 (≤⇒≤′ z≤n)         $ tt
        ≡⟨ cong (bu-demolish-loop n≥0) (sym (unTip∘bu-construct-loop-natural n≥0 e _)) ⟩
      bu-demolish-loop n≥0 ∘ map-buRec n≥0 e ∘ unTip ∘ bu-construct-loop n≥0 ∘ blanks n 0 (≤⇒≤′ z≤n) $ tt
        ≡⟨ refl ⟩
      bu-demolish n ∘ bu-construct n                                                                 $ tt
    ∎
    where n≥0 = ≤⇒≤‴ z≤n
          open ≡-Reasoning

  bu-demolish-loop' : (n≥k : n ≥‴ k) → R ⇉ S → buRec n≥k R ⇉ S
  bu-demolish-loop'  ≤‴-refl        h = h
  bu-demolish-loop' (≤‴-step n≥1+k) h = bu-demolish-loop' n≥1+k (g ∘ mapBT h)

  bu-demolish' : (n : ℕ) → ∀[ Vec A n ] buRec (≤⇒≤‴ z≤n) (const ⊤) ⇉ S
  bu-demolish' n = bu-demolish-loop' (≤⇒≤‴ z≤n) e

  bu-demolish-loop-equiv :
      (n≥k : n ≥‴ k) (h : R ⇉ S) {xs : Vec A n} (r : buRec n≥k R xs)
    → bu-demolish-loop' n≥k h $ r ≡ bu-demolish-loop n≥k ∘ map-buRec n≥k h $ r
  bu-demolish-loop-equiv  ≤‴-refl        h r = refl
  bu-demolish-loop-equiv (≤‴-step n≥1+k) h r =
    begin
      bu-demolish-loop' (≤‴-step n≥1+k) h                                    $ r
        ≡⟨ refl ⟩
      bu-demolish-loop' n≥1+k (g ∘ mapBT h)                                  $ r
        ≡⟨ bu-demolish-loop-equiv n≥1+k (g ∘ mapBT h) _ ⟩
      bu-demolish-loop n≥1+k ∘ map-buRec n≥1+k (g ∘ mapBT h)                 $ r
        ≡⟨ cong (bu-demolish-loop n≥1+k) (map-buRec-∘ n≥1+k g (mapBT h) _) ⟩
      bu-demolish-loop n≥1+k ∘ map-buRec n≥1+k g ∘ map-buRec n≥1+k (mapBT h) $ r
        ≡⟨ refl ⟩
      bu-demolish-loop (≤‴-step n≥1+k) ∘ map-buRec (≤‴-step n≥1+k) h         $ r
    ∎
    where open ≡-Reasoning

  bu-demolish-equiv :
      (n : ℕ) {xs : Vec A n} (r : buRec (≤⇒≤‴ z≤n) (const ⊤) xs)
    → bu-demolish' n r ≡ bu-demolish n r
  bu-demolish-equiv n = bu-demolish-loop-equiv (≤⇒≤‴ z≤n) e

  td≗bu-demolish :
      (n≥k : n ≥‴ k) {xs : Vec A n}
    → ((Σ[ X ∈ Set ] (X → S xs))
      ∋ (tdRec n xs             , td-demolish n))
      ≡ (buRec n≥k (tdRec k) xs , bu-demolish-loop' n≥k (td-demolish k))
  td≗bu-demolish  ≤‴-refl        = refl
  td≗bu-demolish (≤‴-step n≥1+k) = td≗bu-demolish n≥1+k

  td≗bu : (n : ℕ) {xs : Vec A n} → td n {xs} $ tt ≡ bu n $ tt
  td≗bu n =
    begin
      td n                            $ tt
        ≡⟨ td-separation n ⟩
      td-demolish n ∘ td-construct n  $ tt
        ≡⟨ overall (td-demolish n) (bu-demolish-loop' n≥0 e) (td≗bu-demolish n≥0)
             (tdRec-isProp n) (td-construct n tt) (bu-construct n tt) ⟩
      bu-demolish' n ∘ bu-construct n $ tt
        ≡⟨ bu-demolish-equiv n _ ⟩
      bu-demolish n ∘ bu-construct n  $ tt
        ≡⟨ sym (bu-separation n) ⟩
      bu n                            $ tt
    ∎
    where n≥0 = ≤⇒≤‴ z≤n
          open ≡-Reasoning

module Checks where

  pattern 1+ n = suc n

  ImmediateSublistInduction : Set₁
  ImmediateSublistInduction =
    {a : Set} (s : ∀ {k} → Vec a k → Set)
    (e : {xs : Vec a 0} → ⊤ → s xs) (g : ∀ {k xs} → BT (1 + k) k s xs → s xs)
    (n : ℕ) {xs : Vec a n} → ⊤ → s xs

  td : ImmediateSublistInduction
  td s e g  0     = e
  td s e g (1+ n) = g ∘ mapBT (td s e g n) ∘ blanks (1 + n) n (≤′-step ≤′-refl)

  bu : ImmediateSublistInduction
  bu s e g n = unTip ∘ loop 0 (≤⇒≤‴ z≤n) ∘ mapBT e ∘ blanks n 0 (≤⇒≤′ z≤n)
    where
      loop : (k : ℕ) → k ≤‴ n → BT n k s xs → BT n n s xs
      loop n  ≤‴-refl        = id
      loop k (≤‴-step n≥1+k) = loop (1 + k) n≥1+k ∘ mapBT g ∘ retabulate (≤‴⇒≤ n≥1+k)

  retabulate-blanks :
    ∀ {n>k n≥k 1+k≥k n≥1+k}
    → retabulate n>k (blanks n k n≥k {xs} tt)
    ≡ mapBT (blanks (1 + k) k 1+k≥k) (blanks n (1 + k) n≥1+k tt)
  retabulate-blanks = BT-isProp (BT-isProp refl)
