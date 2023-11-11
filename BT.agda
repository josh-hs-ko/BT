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
  A B C   : Set
  k m n   : ℕ
  x       : A
  xs ys   : Vec A _
  P Q R S : A → Set

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
  Tip₀ :          P [] → BT      n       0  P xs
  Tipₙ : ∀ {xs} → P xs → BT (suc n) (suc n) P xs
  Bin  : BT n (suc k) P xs → BT n k (λ ys → P (x ∷ ys)) xs
       → BT (suc n) (suc k) P (x ∷ xs)

-- testBT : BT 4 2 (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) P
-- testBT = Bin (Bin (Tipₙ {!   !}) (Bin (Tipₙ {!   !}) (Tip₀ {!   !})))
--              (Bin (Bin (Tipₙ {!   !}) (Tip₀ {!   !})) (Tip₀ {!   !}))

bounded : BT n k P xs → n ≥ k
bounded (Tip₀ _)  = z≤n
bounded (Tipₙ _)  = ≤-refl
bounded (Bin _ u) = s≤s (bounded u)

unbounded : BT n (suc n) P xs → ⊥
unbounded t = ≤⇒≯ (bounded t) ≤-refl

IsProp : Set → Set
IsProp A = (x y : A) → x ≡ y

IsProp-BT : (∀ {x} → IsProp (P x)) → ∀ {xs} → IsProp (BT n k P xs)
IsProp-BT IsProp-P (Tip₀ p)  (Tip₀ p')   = cong Tip₀ (IsProp-P p p')
IsProp-BT IsProp-P (Tipₙ p)  (Tipₙ p')   = cong Tipₙ (IsProp-P p p')
IsProp-BT IsProp-P (Bin t u) (Bin t' u') = cong₂ Bin (IsProp-BT IsProp-P t t')
                                                     (IsProp-BT IsProp-P u u')
IsProp-BT IsProp-P (Tipₙ p)  (Bin t' _)  = ⊥-elim (unbounded t')
IsProp-BT IsProp-P (Bin t u) (Tipₙ p')   = ⊥-elim (unbounded t)

-- mapBT : (∀ {xs} → P xs → Q xs) → ∀ {xs} → BT n k P xs → BT n k Q xs
mapBT : ∀[ P ⇉ Q ] → ∀[ BT n k P ⇉ BT n k Q ]
mapBT f (Tip₀ p)  = Tip₀ (f p)
mapBT f (Tipₙ p)  = Tipₙ (f p)
mapBT f (Bin t u) = Bin (mapBT f t) (mapBT f u)

cong-mapBT : {f g : ∀[ P ⇉ Q ]} → (∀ {ys} (p : P ys) → f p ≡ g p)
           → (t : BT n k P xs) → mapBT f t ≡ mapBT g t
cong-mapBT f≗g (Tip₀ p)  = cong Tip₀ (f≗g p)
cong-mapBT f≗g (Tipₙ p)  = cong Tipₙ (f≗g p)
cong-mapBT f≗g (Bin t u) = cong₂ Bin (cong-mapBT f≗g t) (cong-mapBT f≗g u)

mapBT-∘ : (f : ∀[ Q ⇉ R ]) (g : ∀[ P ⇉ Q ])
        → (t : BT n k P xs) → mapBT (f ∘ g) $ t ≡ mapBT f ∘ mapBT g $ t
mapBT-∘ f g (Tip₀ p)  = refl
mapBT-∘ f g (Tipₙ p)  = refl
mapBT-∘ f g (Bin t u) = cong₂ Bin (mapBT-∘ f g t) (mapBT-∘ f g u)

unTip : ∀[ BT n n P ⇉ P ]
unTip (Tipₙ p)  = p
unTip (Tip₀ {xs = []} p) = p
unTip (Bin t _) = ⊥-elim (unbounded t)

unTip-naturality : (h : ∀[ P ⇉ Q ]) {xs : Vec A n} (t : BT n n P xs)
                 → unTip ∘ mapBT h $ t ≡ h ∘ unTip $ t
unTip-naturality h (Tipₙ p)  = refl
unTip-naturality h (Tip₀ {xs = []} p) = refl
unTip-naturality h (Bin t _) = ⊥-elim (unbounded t)

zipBTWith : ∀[ P ⇉ Q ⇉ R ] → ∀[ BT n k P ⇉ BT n k Q ⇉ BT n k R ]
zipBTWith f (Tip₀ p)   (Tip₀ q)   = Tip₀ (f p q)
zipBTWith f (Tipₙ p)   u          = Tipₙ (f p (unTip u))
zipBTWith f (Bin t _ ) (Tipₙ _)   = ⊥-elim (unbounded t)
zipBTWith f (Bin t t') (Bin u u') = Bin (zipBTWith f t u) (zipBTWith f t' u')

choose : (n k : ℕ) → n ≥′ k → ∀⟨ Vec A n ⟩[ BT n k (const ⊤) ]
choose _        zero    _                      = Tip₀ tt
choose (suc k) (suc k)  ≤′-refl                = Tipₙ tt
choose (suc n) (suc k) (≤′-step n≥1+k) {_ ∷ _} = Bin (choose n (suc k) n≥1+k) (choose n k n≥k)
  where n≥k = ≤′-trans (≤′-step ≤′-refl) n≥1+k

choose↑ : (n k : ℕ) → n ≥′ k → ∀⟨ Vec A n ⟩[ const ⊤ ⇉ BT n k (const ⊤) ]
choose↑ n k n≥k _ = choose n k n≥k

IsProp-≤ : {m n : ℕ} → IsProp (m ≤ n)
IsProp-≤  z≤n       z≤n       = refl
IsProp-≤ (s≤s m≤n) (s≤s m≤n') = cong s≤s (IsProp-≤ m≤n m≤n')

upgrade : n > k → ∀[ BT n k P ⇉ BT n (suc k) (BT (suc k) k P) ]
upgrade 1+n>1+n       (Tipₙ p)                       = ⊥-elim (<-irrefl refl 1+n>1+n)
upgrade _ {_ ∷ []   } (Tip₀ p)                       = Tipₙ (Tip₀ p)
upgrade _ {_ ∷ _ ∷ _} (Tip₀ p)                       = Bin (upgrade 1+n>0 (Tip₀ p)) (Tip₀ (Tip₀ p)) where 1+n>0 = s≤s z≤n
upgrade _             (Bin   (Tipₙ p)   u)           = Tipₙ (Bin (Tipₙ p) u)
upgrade _             (Bin t@(Bin t' _)   (Tip₀ q))  = Bin (upgrade 1+n>1 t) (mapBT (λ p → Bin (Tipₙ p) (Tip₀ q)) t) where 1+n>1 = s≤s (bounded t')
upgrade _             (Bin t@(Bin _  _)   (Tipₙ q))  = ⊥-elim (unbounded t)
upgrade (s≤s 1+n>1+k) (Bin t@(Bin t' _) u@(Bin _ _)) = Bin (upgrade 1+n>2+k t) (zipBTWith (λ p → Bin (Tipₙ p)) t (upgrade 1+n>1+k u)) where 1+n>2+k = s≤s (bounded t')

upgrade-naturality : (n>k : n > k) {xs : Vec A n} (h : ∀[ P ⇉ Q ]) (t : BT n k P xs)
                   → upgrade n>k ∘ mapBT h $ t ≡ mapBT (mapBT h) ∘ upgrade n>k $ t
upgrade-naturality = {!   !}
-- upgrade-naturality 1+n>1+n       h (Tipₙ p)                       = ⊥-elim (<-irrefl refl 1+n>1+n)
-- upgrade-naturality _ {_ ∷ []   } h (Tip₀ p)                       = refl
-- upgrade-naturality _ {_ ∷ _ ∷ _} h (Tip₀ p)                       = cong₂ Bin (upgrade-naturality 1+n>0 h (Tip₀ p)) refl where 1+n>0 = s≤s z≤n
-- upgrade-naturality _             h (Bin   (Tipₙ p)   u)           = refl
-- upgrade-naturality _             h (Bin t@(Bin t' _)   (Tip₀ q))  = cong₂ Bin (trans (cong (λ ineq → upgrade ineq (mapBT h t)) (IsProp-≤ _ _)) (upgrade-naturality 1+n>1 h t)) (trans (sym (mapBT-∘ (λ p → Bin (Tipₙ p) (Tip₀ (h q))) h t)) (mapBT-∘ (mapBT h) (λ p → Bin (Tipₙ p) (Tip₀ q)) t)) where 1+n>1 = s≤s (bounded t')
-- upgrade-naturality _             h (Bin t@(Bin _  _)   (Tipₙ q))  = ⊥-elim (unbounded t)
-- upgrade-naturality (s≤s 1+n>1+k) h (Bin t@(Bin t' _) u@(Bin _ _)) = cong₂ Bin (trans (cong (λ ineq → upgrade ineq (mapBT h t)) (IsProp-≤ _ _)) (upgrade-naturality 1+n>2+k h t)) {!   !} where 1+n>2+k = s≤s (bounded t')

module Algorithms
  {A : Set} (S : {k : ℕ} → Vec A k → Set)
  (e : S []) (g : {k : ℕ} → ∀[ BT (suc k) k S ⇉ S ])
  -- (e : S []) (g : {k : ℕ} {xs : Vec A (suc k)} → BT (suc k) k S xs → S xs)
  -- (e : S) (g : List S → S)
  where

  e↑ : ∀⟨ Vec A 0 ⟩[ const ⊤ ⇉ S ]
  e↑ {[]} _ = e

  td : (n : ℕ) → ∀⟨ Vec A n ⟩[ const ⊤ ⇉ S ]
  td  zero   = e↑
  td (suc n) = g ∘ mapBT (td n) ∘ choose↑ (suc n) n 1+n≥n
    where 1+n≥n = ≤′-step ≤′-refl

  bu-loop : n ≥‴ k → ∀[ BT n k S ⇉ BT n n S ]
  bu-loop  ≤‴-refl        = id
  bu-loop (≤‴-step n≥1+k) = bu-loop n≥1+k ∘ mapBT g ∘ upgrade (≤‴⇒≤ n≥1+k)

  bu : (n : ℕ) → ∀⟨ Vec A n ⟩[ const ⊤ ⇉ S ]
  bu n = unTip ∘ bu-loop (≤⇒≤‴ z≤n) ∘ mapBT e↑ ∘ choose↑ n 0 (≤⇒≤′ z≤n)
  -- bu _ = unTip (bu-loop (≤⇒≤‴ z≤n) (Tip₀ e))

--------
-- Correctness: separating both algorithms into production and consumption phases

module Production where

  tdRec : (n : ℕ) → Vec A n → Set
  tdRec  zero   = const ⊤
  tdRec (suc n) = BT (suc n) n (tdRec n)

  td-produce : (n : ℕ) → ∀⟨ Vec A n ⟩[ const ⊤ ⇉ tdRec n ]
  td-produce  zero   = id
  td-produce (suc n) = mapBT (td-produce n) ∘ choose↑ (suc n) n 1+n≥n
    where 1+n≥n = ≤′-step ≤′-refl

  IsProp-tdRec : (n : ℕ) {xs : Vec A n} → IsProp (tdRec n xs)
  IsProp-tdRec  zero   = λ _ _ → refl
  IsProp-tdRec (suc n) = IsProp-BT (IsProp-tdRec n)

  buRec : n ≥‴ k → (Vec A k → Set) → Vec A n → Set
  buRec          ≤‴-refl        = id
  buRec {k = k} (≤‴-step n≥1+k) = buRec n≥1+k ∘ BT (suc k) k

  bu-produce-loop : (n≥k : n ≥‴ k) → ∀[ BT n k P ⇉ BT n n (buRec n≥k P) ]
  bu-produce-loop  ≤‴-refl        = id
  bu-produce-loop (≤‴-step n≥1+k) = bu-produce-loop n≥1+k ∘ upgrade (≤‴⇒≤ n≥1+k)

  bu-produce : (n : ℕ) → ∀⟨ Vec A n ⟩[ const ⊤ ⇉ buRec (≤⇒≤‴ z≤n) (const ⊤) ]
  bu-produce n = unTip ∘ bu-produce-loop (≤⇒≤‴ z≤n) ∘ choose↑ n 0 (≤⇒≤′ z≤n)

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

  bu-produce-loop-naturality :
      (n≥k : n ≥‴ k) (h : ∀[ P ⇉ Q ]) {xs : Vec A n} (t : BT n k P xs)
    → bu-produce-loop n≥k ∘ mapBT h $ t ≡ mapBT (map-buRec n≥k h) ∘ bu-produce-loop n≥k $ t
  bu-produce-loop-naturality  ≤‴-refl        h t = refl
  bu-produce-loop-naturality (≤‴-step n≥1+k) h t =
    begin
      bu-produce-loop (≤‴-step n≥1+k) ∘ mapBT h                                        $ t
        ≡⟨ refl ⟩
      bu-produce-loop n≥1+k ∘ upgrade (≤‴⇒≤ n≥1+k) ∘ mapBT h                           $ t
        ≡⟨ cong (bu-produce-loop n≥1+k) (upgrade-naturality (≤‴⇒≤ n≥1+k) h t) ⟩
      bu-produce-loop n≥1+k ∘ mapBT (mapBT h) ∘ upgrade (≤‴⇒≤ n≥1+k)                   $ t
        ≡⟨ bu-produce-loop-naturality n≥1+k (mapBT h) _ ⟩
      mapBT (map-buRec n≥1+k (mapBT h)) ∘ bu-produce-loop n≥1+k ∘ upgrade (≤‴⇒≤ n≥1+k) $ t
        ≡⟨ refl ⟩
      mapBT (map-buRec (≤‴-step n≥1+k) h) ∘ bu-produce-loop (≤‴-step n≥1+k)            $ t
    ∎
    where open ≡-Reasoning

  unTip∘bu-produce-loop-naturality :
      (n≥k : n ≥‴ k) (h : ∀[ P ⇉ Q ]) {xs : Vec A n} (t : BT n k P xs)
    →                   unTip ∘ bu-produce-loop n≥k ∘ mapBT h $ t
    ≡ map-buRec n≥k h ∘ unTip ∘ bu-produce-loop n≥k           $ t
  unTip∘bu-produce-loop-naturality n≥k h t =
      begin
        unTip ∘ bu-produce-loop n≥k ∘ mapBT h                 $ t
          ≡⟨ cong unTip (bu-produce-loop-naturality n≥k h _) ⟩
        unTip ∘ mapBT (map-buRec n≥k h) ∘ bu-produce-loop n≥k $ t
          ≡⟨ unTip-naturality (map-buRec n≥k h) (bu-produce-loop n≥k t) ⟩
        map-buRec n≥k h ∘ unTip ∘ bu-produce-loop n≥k         $ t
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
      g ∘ mapBT (td n) ∘ choose↑ (suc n) n 1+n≥n                                $ tt
        ≡⟨ cong g (cong-mapBT (λ _ → td-separation n) _) ⟩
      g ∘ mapBT (td-consume n ∘ td-produce n) ∘ choose↑ (suc n) n 1+n≥n         $ tt
        ≡⟨ cong g (mapBT-∘ (td-consume n) (td-produce n) _) ⟩
      g ∘ mapBT (td-consume n) ∘ mapBT (td-produce n) ∘ choose↑ (suc n) n 1+n≥n $ tt
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
      unTip ∘ bu-loop (≤‴-step n≥1+k)                                                                  $ t
        ≡⟨ refl ⟩
      unTip ∘ bu-loop n≥1+k ∘ mapBT g ∘ upgrade (≤‴⇒≤ n≥1+k)                                           $ t
        ≡⟨ bu-loop-separation n≥1+k _ ⟩
      bu-consume-loop n≥1+k ∘ unTip ∘ bu-produce-loop n≥1+k ∘ mapBT g ∘ upgrade (≤‴⇒≤ n≥1+k)           $ t
        ≡⟨ cong (bu-consume-loop n≥1+k) (unTip∘bu-produce-loop-naturality n≥1+k g _) ⟩
      bu-consume-loop n≥1+k ∘ map-buRec n≥1+k g ∘ unTip ∘ bu-produce-loop n≥1+k ∘ upgrade (≤‴⇒≤ n≥1+k) $ t
        ≡⟨ refl ⟩
      bu-consume-loop (≤‴-step n≥1+k) ∘ unTip ∘ bu-produce-loop (≤‴-step n≥1+k)                        $ t
    ∎
    where open ≡-Reasoning

  bu-separation : (n : ℕ) {xs : Vec A n} → bu n {xs} $ tt ≡ bu-consume n ∘ bu-produce n $ tt
  bu-separation n =
    begin
      bu n                                                                                          $ tt
        ≡⟨ refl ⟩
      unTip ∘ bu-loop n≥0 ∘ mapBT e↑ ∘ choose↑ n 0 (≤⇒≤′ z≤n)                                       $ tt
        ≡⟨ bu-loop-separation n≥0 _ ⟩
      bu-consume-loop n≥0 ∘ unTip ∘ bu-produce-loop n≥0 ∘ mapBT e↑ ∘ choose↑ n 0 (≤⇒≤′ z≤n)         $ tt
        ≡⟨ cong (bu-consume-loop n≥0) (unTip∘bu-produce-loop-naturality n≥0 e↑ _) ⟩
      bu-consume-loop n≥0 ∘ map-buRec n≥0 e↑ ∘ unTip ∘ bu-produce-loop n≥0 ∘ choose↑ n 0 (≤⇒≤′ z≤n) $ tt
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

  td≡bu-consume :
      (n≥k : n ≥‴ k) {xs : Vec A n}
    → ((Σ[ X ∈ Set ] (X → S xs))
      ∋ (tdRec n xs             , td-consume n))
      ≡ (buRec n≥k (tdRec k) xs , bu-consume-loop' n≥k (td-consume k))
  td≡bu-consume  ≤‴-refl        = refl
  td≡bu-consume (≤‴-step n≥1+k) = td≡bu-consume n≥1+k

  td≡bu : (n : ℕ) {xs : Vec A n} → td n {xs} $ tt ≡ bu n $ tt
  td≡bu n =
    begin
      td n                         $ tt
        ≡⟨ td-separation n ⟩
      td-consume n ∘ td-produce n  $ tt
        ≡⟨ overall (td-consume n) (bu-consume-loop' n≥0 e↑) (td≡bu-consume n≥0)
             (IsProp-tdRec n) (td-produce n tt) (bu-produce n tt) ⟩
      bu-consume' n ∘ bu-produce n $ tt
        ≡⟨ bu-consume-equiv n _ ⟩
      bu-consume n ∘ bu-produce n  $ tt
        ≡⟨ sym (bu-separation n) ⟩
      bu n                         $ tt
    ∎
    where n≥0 = ≤⇒≤‴ z≤n
          open ≡-Reasoning

-- bu-loop-separation' :
--     (n≥k : n ≥‴ k) (h : ∀[ R ⇉ S ])
--   → {xs : Vec A n} (t : BT n k R xs)
--   → unTip ∘ bu-loop n≥k ∘ mapBT h $ t ≡ bu-consume-loop' n≥k h ∘ unTip ∘ bu-produce-loop n≥k $ t
-- bu-loop-separation'  ≤‴-refl        h t = {!   !}
-- bu-loop-separation' (≤‴-step n≥1+k) h t =
--   begin
--     unTip ∘ bu-loop (≤‴-step n≥1+k) ∘ mapBT h $ t
--       ≡⟨ refl ⟩
--     unTip ∘ bu-loop n≥1+k ∘ mapBT g ∘ upgrade (≤‴⇒≤ n≥1+k) ∘ mapBT h $ t
--       ≡⟨ cong (unTip ∘ bu-loop n≥1+k ∘ mapBT g) {!   !} ⟩
--     unTip ∘ bu-loop n≥1+k ∘ mapBT g ∘ mapBT (mapBT h) ∘ upgrade (≤‴⇒≤ n≥1+k) $ t
--       ≡⟨ sym (cong (unTip ∘ bu-loop n≥1+k) (mapBT-∘ g (mapBT h) _)) ⟩
--     unTip ∘ bu-loop n≥1+k ∘ mapBT (g ∘ mapBT h) ∘ upgrade (≤‴⇒≤ n≥1+k) $ t
--       ≡⟨ bu-loop-separation' n≥1+k (g ∘ mapBT h) _ ⟩
--     bu-consume-loop' n≥1+k (g ∘ mapBT h) ∘ unTip ∘ bu-produce-loop n≥1+k ∘ upgrade (≤‴⇒≤ n≥1+k) $ t
--       ≡⟨ refl ⟩
--     bu-consume-loop' (≤‴-step n≥1+k) h ∘ unTip ∘ bu-produce-loop (≤‴-step n≥1+k) $ t
--   ∎
--   where open ≡-Reasoning

-- bu-separation' : (n : ℕ) {xs : Vec A n} → bu n {xs} $ tt ≡ bu-consume' n ∘ bu-produce n $ tt
-- bu-separation' n =
--   begin
--     bu n tt
--       ≡⟨ refl ⟩
--     unTip ∘ bu-loop n≥0 ∘ mapBT e↑ ∘ choose↑ n 0 (≤⇒≤′ z≤n) $ tt
--       ≡⟨ bu-loop-separation' (≤⇒≤‴ z≤n) e↑ _ ⟩
--     bu-consume-loop' n≥0 e↑ ∘ unTip ∘ bu-produce-loop n≥0 ∘ choose↑ n 0 (≤⇒≤′ z≤n) $ tt
--       ≡⟨ refl ⟩
--     bu-consume' n ∘ bu-produce n $ tt
--   ∎
--   where n≥0 = ≤⇒≤‴ z≤n
--         open ≡-Reasoning

-- upgrade-choose :
--   ∀ {n k 1+k≥k n≥1+k n>k n≥k} {xs : Vec A n} t
--   → (BT n (suc k) (BT (suc k) k (const ⊤)) xs ∋
--     mapBT (choose↑ (suc k) k 1+k≥k) (choose↑ n (suc k) n≥1+k t))
--   ≡ upgrade n>k (choose↑ n k n≥k t)
-- upgrade-choose _ = IsProp-BT (IsProp-BT (const (const refl))) _ _

-- unTip-upgrade :
--   ∀ {n 1+n>n xs} {P : Vec A n → Set} (t : BT (suc n) n P xs)
--   → unTip (upgrade 1+n>n t) ≡ t
-- unTip-upgrade {xs = _ ∷ []} (Tip₀ p) = refl
-- unTip-upgrade (Bin (Tipₙ p) u) = refl
-- unTip-upgrade (Bin (Bin t _) (Bin _ _)) = ⊥-elim (unbounded t)

-- module Algorithms
--   {A : Set} (S : {k : ℕ} → Vec A (suc k) → Set)
--   (g : {k : ℕ} {xs : Vec A (2 + k)} → BT (2 + k) (1 + k) S xs → S xs)
--   (g : {k : ℕ} → ∀[ BT (2 + k) (1 + k) S ⇉ S ])
--   where

--   head' : ∀⟨ Vec A 1 ⟩[ All (S ∘ V.[_]) ⇉ S ]
--   head' (s ∷ []) = s

--   td : ∀⟨ Vec A (suc n) ⟩[ All (S ∘ V.[_]) ⇉ S ]
--   td {zero } = head'
--   td {suc n} = g ∘ mapBT (td {n}) ∘ choose (2 + n) (1 + n) 2+n≥1+n
--     where 2+n≥1+n = ≤′-step ≤′-refl

--   bu-loop : n ≥‴ k → ∀[ BT (suc n) (suc k) S ⇉ BT (suc n) (suc n) S ]
--   bu-loop  ≤‴-refl        = id
--   bu-loop (≤‴-step n≥1+k) = bu-loop n≥1+k ∘ mapBT g ∘ upgrade (s≤s (≤‴⇒≤ n≥1+k))

--   bu : ∀⟨ Vec A (suc n) ⟩[ All (S ∘ V.[_]) ⇉ S ]
--   bu = unTip ∘ bu-loop (≤⇒≤‴ z≤n) ∘ mapBT head' ∘ choose _ 1 (≤⇒≤′ (s≤s z≤n))

-- module ChooseFromSum where

--   -- BT A m k is a tree corresponding to C (m+k) k in
--   -- Pascal's triangle.

--   data BT (A : Set) : ℕ → ℕ → Set where
--     Tip₀ : A → BT A      n       0   -- C    n     0
--     Tipₙ : A → BT A      0  (suc n)  -- C (1+n) (1+n)
--     Bin  :     BT A      m  (suc k)  -- C    n  (1+k) , or C (1+m+k) (1+k)
--              → BT A (suc m)      k   -- C    n     k  , or C (1+m+k)    k
--              → BT A (suc m) (suc k)  -- C (1+n) (1+k) , or C (2+m+k) (1+k)

--   -- forward declarations

--   zipBT : (A → B → C) → BT A m k → BT B m k → BT C m k

--   mapBT : (A → B) → BT A m k → BT B m k

--   -- our "cd" function!

--   cd : BT A (suc m) (suc k)          -- C n k
--      → BT (List A) m (suc (suc k))   -- C n (1+k)
--   cd (Bin (Tipₙ x) (Tip₀ y)) = Tipₙ (x ∷ y ∷ [])
--   cd (Bin (u@(Bin _ _)) (Tip₀ y)) = Bin (cd u) (mapBT (λ x → x ∷ y ∷ []) u)
--   cd (Bin (Tipₙ x) (v@(Bin _ _))) with cd v
--   ... | Tipₙ xs = Tipₙ (x ∷ xs)
--   cd (Bin (u@(Bin _ _)) (v@(Bin _ _))) =
--     Bin (cd u) (zipBT _∷_ u (cd v))

--   {-

--   Haskell code:

--   data B a = Tip a | Bin (B a) (B a)

--   cd :: B a → B [a]
--   cd (Bin (Tip a) (Tip b)) = Tip [a,b]
--   cd (Bin u (Tip b)) = Bin (cd u) (map (:[b]) u)
--   cd (Bin (Tip a) v) = Tip (a:as) where Tip as = cd v
--   cd (Bin u v) = Bin (cd u) (zipBWith (:) u (cd v))

--   -}

--   -- utility functions

--   zipBT f (Tip₀ x) (Tip₀ y) = Tip₀ (f x y)
--   zipBT f (Tipₙ x) (Tipₙ y) = Tipₙ (f x y)
--   zipBT f (Bin t u) (Bin v w) = Bin (zipBT f t v) (zipBT f u w)

--   mapBT f (Tip₀ x) = Tip₀ (f x)
--   mapBT f (Tipₙ x) = Tipₙ (f x)
--   mapBT f (Bin t u) = Bin (mapBT f t) (mapBT f u)


-- module ChooseDirectly where

--   data BT (A : Set) : ℕ → ℕ → Set where
--     Tip₀ : A                         → BT A      n       0
--     Tipₙ : A                         → BT A (suc n) (suc n)
--     Bin  : BT A n (suc k) → BT A n k → BT A (suc n) (suc k)

--   mapBT : (A → B) → BT A n k → BT B n k
--   mapBT f (Tip₀ x)  = Tip₀ (f x)
--   mapBT f (Tipₙ x)  = Tipₙ (f x)
--   mapBT f (Bin t u) = Bin (mapBT f t) (mapBT f u)

--   -- choose : (xs : Vec A n) (k : ℕ) → BT (Vec A k) n k
--   -- choose _   zero   = Tip₀ []
--   -- choose xs (suc k) = {!   !}

-- module Relational where

--   module Path where

--     data Choose : (n k : ℕ) → Vec A n → Vec A k → Set where
--       none    :                                        Choose      n       0       xs       []
--       all'    :                                        Choose (suc n) (suc n)      xs       xs
--       discard :         Choose n (suc k) xs (y ∷ ys) → Choose (suc n) (suc k) (x ∷ xs) (y ∷ ys)
--       keep    : n > k → Choose n      k  xs      ys  → Choose (suc n) (suc k) (x ∷ xs) (x ∷ ys)

--     -- test : Choose 2 2 (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ [])
--     -- test = keep {!   !} {!   !}

--     -- -- The sum version doesn’t work
--     -- data Choose : (m k : ℕ) → Vec A (m + k) → Vec A k → Set where
--     --   Tip₀ :                                     Choose      0       0       xs       []
--     --   Tipₙ :                                     Choose      0  (suc n)      xs       xs
--     --   Binᴸ : Choose      m (suc k) xs (y ∷ ys) → Choose (suc m) (suc k) (x ∷ xs) (y ∷ ys)
--     --   Binᴿ : Choose (suc m)     k {!   !}  ys  → Choose (suc m) (suc k) (x ∷ xs) (x ∷ ys)

--   module ChooseAsFunction where

--     open ChooseDirectly

--     fun : (A → B) → (A → B → Set)
--     fun f a b = f a ≡ b

--     _>>=ᴾ_ : (A → Set) → (A → B → Set) → (B → Set)
--     (P >>=ᴾ R) b = ∃ λ a → P a × R a b

--     Choose : (n k : ℕ) → Vec A n → BT (Vec A k) n k → Set
--     Choose _            .0       xs  (Tip₀ []) = ⊤
--     Choose (suc n) (suc .n)      xs  (Tipₙ ys) = xs ≡ ys
--     Choose (suc n) (suc  k) (x ∷ xs) (Bin t u) =
--       Choose n (suc k) xs t × (Choose n k xs >>=ᴾ fun (mapBT (x ∷_))) u

--   open ChooseDirectly

--   data Choose : (n k : ℕ) → Vec A n → BT (Vec A k) n k → Set where
--     Tip₀ : Choose      n       0  xs (Tip₀ [])
--     Tipₙ : Choose (suc n) (suc n) xs (Tipₙ xs)
--     Bin  : ∀ {t u} → Choose n (suc k) xs t → Choose n k xs u
--           → Choose (suc n) (suc k) (x ∷ xs) (Bin t (mapBT (x ∷_) u))

-- module ImmediateSublists where

--   data Sub' : (n : ℕ) → (P : ∀ n → Vec A n → Set) → Vec A n → Set where
--     []  : ∀ {P} → Sub' 0 P xs
--     _∷_ : ∀ {P} → P _ xs → Sub' n (λ _ ys → P _ (x ∷ ys)) xs → Sub' (suc n) P (x ∷ xs)

--   data Sub : (n : ℕ) → (Vec A n → Set) → Vec A (suc n) → Set where
--     ⟨_⟩ : P [] → Sub 0 P xs
--     _∷_ : P xs → Sub n (λ ys → P (x ∷ ys)) xs → Sub (suc n) P (x ∷ xs)

--   -- testSub' : ∀ {P} → Sub' 5 P (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
--   -- testSub' = {!   !} ∷ {!   !} ∷ {!   !} ∷ {!   !} ∷ {!   !} ∷ []

--   -- testSub : Sub 4 P (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
--   -- testSub = {!   !} ∷ {!   !} ∷ {!   !} ∷ {!   !} ∷ ⟨ {!   !} ⟩

--   upgrade : n > k → BT n k P xs → BT n (suc k) (Sub k P) xs
--   upgrade            1+n>1+n (Tipₙ p)                       = ⊥-elim (<-irrefl refl 1+n>1+n)
--   upgrade {xs = _ ∷ []}    _ (Tip₀ p)                       = Tipₙ ⟨ p ⟩
--   upgrade {xs = _ ∷ _ ∷ _} _ (Tip₀ p)                       = Bin (upgrade (s≤s z≤n) (Tip₀ p)) (Tip₀ ⟨ p ⟩)
--   upgrade                  _ (Bin   (Tipₙ p)   u)           = Tipₙ (p ∷ lemma u)
--     where
--       lemma : BT (suc k) k P xs → Sub k P xs
--       lemma (Tip₀ p) = ⟨ p ⟩
--       lemma (Bin (Tipₙ x) u) = x ∷ (lemma u)
--       lemma (Bin t@(Bin t₀ t₁) u) = ⊥-elim (unbounded t₀)
--   upgrade                  _ (Bin t@(Bin t' _)   (Tip₀ q )) = Bin (upgrade (s≤s (bounded t')) t) (mapBT (_∷ ⟨ q ⟩) t)
--   upgrade                  _ (Bin t@(Bin _  _)   (Tipₙ q )) = ⊥-elim (unbounded t)
--   upgrade      (s≤s 1+n>1+k) (Bin t@(Bin t' _) u@(Bin _ _)) = Bin (upgrade (s≤s (bounded t')) t) (zipBTWith _∷_ t (upgrade 1+n>1+k u))
