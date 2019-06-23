open import Prelude

module Nat where

  -- definitions

  data Nat : Set where
    Z : Nat
    1+ : Nat → Nat

  {-# BUILTIN NATURAL Nat #-}

  _+_ : Nat → Nat → Nat
  Z + m = m
  1+ n + m = 1+ (n + m)

  infixl 60 _+_

  data _≤_ : Nat → Nat → Set where
    ≤refl  : ∀{n} → n ≤ n
    ≤1+    : ∀{n m} → n ≤ m → n ≤ 1+ m

  infix 40 _≤_

  _<_ : Nat → Nat → Set
  n < m = n ≤ m ∧ n ≠ m
  infix 40 _<_

  difference : ∀{n m} → n ≤ m → Nat
  difference {n} {.n} ≤refl = Z
  difference {n} {.(1+ _)} (≤1+ n≤m-1) = 1+ (difference n≤m-1)

  -- basic theorems

  -- the succ operation is injective
  1+inj : ∀{n m} → 1+ n == 1+ m → n == m
  1+inj refl = refl

  1+ap : ∀{n m} → n == m → 1+ n == 1+ m
  1+ap {n} {.n} refl = refl

  1+ap-cp : ∀{n m} → 1+ n ≠ 1+ m → n ≠ m
  1+ap-cp h1 h2 = h1 (1+ap h2)

  1+inj-cp : ∀{n m} → n ≠ m → 1+ n ≠ 1+ m
  1+inj-cp h1 h2 = h1 (1+inj h2)

  -- equality of naturals is decidable. we represent this as computing a
  -- choice of units, with inl <> meaning that the naturals are indeed the
  -- same and inr <> that they are not.
  natEQ : (x y : Nat) → ((x == y) ∨ ((x == y) → ⊥))
  natEQ Z Z = Inl refl
  natEQ Z (1+ y) = Inr (λ ())
  natEQ (1+ x) Z = Inr (λ ())
  natEQ (1+ x) (1+ y) with natEQ x y
  natEQ (1+ x) (1+ .x) | Inl refl = Inl refl
  ... | Inr b = Inr (λ x₁ → b (1+inj x₁))

  0≠1+n : ∀{n} → 0 ≠ 1+ n
  0≠1+n = λ ()

  -- _+_ theorems

  n+Z==n : ∀{n} → n + Z == n
  n+Z==n {Z} = refl
  n+Z==n {1+ n} = 1+ap n+Z==n

  n+1+m==1+n+m : ∀{n m} → n + 1+ m == 1+ (n + m)
  n+1+m==1+n+m {Z} = refl
  n+1+m==1+n+m {1+ n} = 1+ap n+1+m==1+n+m

  n≠n+1+m : ∀{n m} → n ≠ n + 1+ m
  n≠n+1+m {Z} {m} ()
  n≠n+1+m {1+ n} {m} h = 1+inj-cp n≠n+1+m h

  +comm : ∀{a b} → a + b == b + a
  +comm {Z} {b} = ! n+Z==n
  +comm {1+ a} {Z} = 1+ap n+Z==n
  +comm {1+ a} {1+ b} with a + 1+ b | b + 1+ a | n+1+m==1+n+m {a} {b} | n+1+m==1+n+m {b} {a}
  +comm {1+ a} {1+ b} | _ | _ | refl | refl = 1+ap (1+ap (+comm {a}))

  +assc : ∀{a b c} → (a + b) + c == a + (b + c)
  +assc {Z} = refl
  +assc {1+ a} = 1+ap (+assc {a})

  a+n==a+m→n==m : ∀{a n m} → a + n == a + m → n == m
  a+n==a+m→n==m {Z} refl = refl
  a+n==a+m→n==m {1+ a} a+n==a+m = a+n==a+m→n==m (1+inj a+n==a+m)

  n+a==m+a→n==m : ∀{n m a} → n + a == m + a → n == m
  n+a==m+a→n==m {n} {m} {a} n+a==m+a rewrite +comm {n} {a} | +comm {m} {a} = a+n==a+m→n==m n+a==m+a

  -- _≤_ theorems

  0≤n : ∀{n} → Z ≤ n
  0≤n {Z} = ≤refl
  0≤n {1+ n} = ≤1+ 0≤n

  1+n≰0 : ∀{n} → 1+ n ≤ Z → ⊥
  1+n≰0 = λ ()

  n≤m→1+n≤1+m : ∀{n m} → n ≤ m → 1+ n ≤ 1+ m
  n≤m→1+n≤1+m {n} {.n} ≤refl = ≤refl
  n≤m→1+n≤1+m {n} {.(1+ _)} (≤1+ h) = ≤1+ (n≤m→1+n≤1+m h)

  1+n≤1+m→n≤m : ∀{n m} → 1+ n ≤ 1+ m → n ≤ m
  1+n≤1+m→n≤m {n} {.n} ≤refl = ≤refl
  1+n≤1+m→n≤m {n} {Z} (≤1+ h) = abort (1+n≰0 h)
  1+n≤1+m→n≤m {n} {1+ m} (≤1+ h) = ≤1+ (1+n≤1+m→n≤m h)

  n+s≤m+s→n≤m : ∀{n m s} → n + s ≤ m + s → n ≤ m
  n+s≤m+s→n≤m {n} {m} {s = Z} n+s≤m+s
    rewrite n+Z==n {n} | n+Z==n {m} = n+s≤m+s
  n+s≤m+s→n≤m {n} {m} {s = 1+ s} n+s≤m+s
    rewrite n+1+m==1+n+m {n} {s} | n+1+m==1+n+m {m} {s}
      = n+s≤m+s→n≤m (1+n≤1+m→n≤m n+s≤m+s)

  1+n≰n : ∀{n} → 1+ n ≤ n → ⊥
  1+n≰n {Z} h = abort (1+n≰0 h)
  1+n≰n {1+ n} h = 1+n≰n (1+n≤1+m→n≤m h)

  ≤total : ∀{n m} → n ≤ m ∨ m ≤ n
  ≤total {Z} {m} = Inl 0≤n
  ≤total {1+ n} {Z} = Inr (≤1+ 0≤n)
  ≤total {1+ n} {1+ m} with ≤total {n} {m}
  ≤total {1+ n} {1+ m} | Inl h = Inl (n≤m→1+n≤1+m h)
  ≤total {1+ n} {1+ m} | Inr h = Inr (n≤m→1+n≤1+m h)

  ≤trans : ∀{a b c} → a ≤ b → b ≤ c → a ≤ c
  ≤trans ≤refl b≤c = b≤c
  ≤trans (≤1+ a≤b) ≤refl = ≤1+ a≤b
  ≤trans (≤1+ a≤b) (≤1+ b≤c) = ≤1+ (≤trans (≤1+ a≤b) b≤c)

  ≤antisym : ∀{n m} → n ≤ m → m ≤ n → n == m
  ≤antisym {n} {.n} ≤refl m≤n = refl
  ≤antisym {n} {.(1+ _)} (≤1+ h1) h2 = abort (1+n≰n (≤trans h2 h1))

  n≤n+m : ∀{n m} → n ≤ n + m
  n≤n+m {n} {Z} with n + Z | n+Z==n {n}
  n≤n+m {_} {Z} | _ | refl = ≤refl
  n≤n+m {n} {1+ m} with n + 1+ m | ! (n+1+m==1+n+m {n} {m})
  n≤n+m {n} {1+ m} | _ | refl = ≤trans n≤n+m (≤1+ ≤refl)

  n≤m+n : ∀{n m} → n ≤ m + n
  n≤m+n {n} {m} rewrite +comm {m} {n} = n≤n+m

  -- _<_ theorems

  n≮0 : ∀{n} → n < Z → ⊥
  n≮0 {Z} (π3 , π4) = π4 refl
  n≮0 {1+ n} (π3 , π4) = 1+n≰0 π3

  n<1+n : ∀{n} → n < 1+ n
  π1 n<1+n = ≤1+ ≤refl
  π2 n<1+n ()

  1+n<1+m→n<m : ∀{n m} → 1+ n < 1+ m → n < m
  π1 (1+n<1+m→n<m (π3 , π4)) = 1+n≤1+m→n≤m π3
  π2 (1+n<1+m→n<m (π3 , π4)) = 1+ap-cp π4

  <trans : ∀{a b c} → a < b → b < c → a < c
  π1 (<trans (π3 , π4) (π5 , π6)) = ≤trans π3 π5
  π2 (<trans (π3 , π4) (≤refl , π6)) = abort (π6 refl)
  π2 (<trans (π3 , π4) (≤1+ π5 , π6)) refl = 1+n≰n (≤trans π3 π5)

  <antisym : ∀{n m} → n < m → m < n → ⊥
  <antisym (n≤m , n≠m) (m≤n , _) = n≠m (≤antisym n≤m m≤n)

  <antirefl : ∀{n} → n < n → ⊥
  <antirefl (_ , ne) = abort (ne refl)

  n<m→n<s+m : ∀{n m s} → n < m → n < s + m
  n<m→n<s+m {s = Z} n<m = n<m
  n<m→n<s+m {s = 1+ s} n<m =
    <trans (n<m→n<s+m {s = s} n<m) n<1+n

  n<m→1+n<1+m : ∀{n m} → n < m → 1+ n < 1+ m
  n<m→1+n<1+m (π3 , π4) = n≤m→1+n≤1+m π3 , 1+inj-cp π4

  0<1+n : ∀{n} → 0 < 1+ n
  0<1+n {Z} = ≤1+ ≤refl , (λ ())
  0<1+n {1+ n} = 0≤n , (λ ())

  1+n≤m→n<m : ∀{n m} → 1+ n ≤ m → n < m
  1+n≤m→n<m ≤refl = n<1+n
  1+n≤m→n<m (≤1+ 1+n≤m) = <trans (1+n≤m→n<m 1+n≤m) n<1+n

  n≤m→n<1+m : ∀{n m} → n ≤ m → n < 1+ m
  n≤m→n<1+m {Z} n≤m = 0<1+n
  n≤m→n<1+m {1+ n} n≤m = n<m→1+n<1+m (1+n≤m→n<m n≤m)

  n<m→1+n≤m : ∀{n m} → n < m → 1+ n ≤ m
  n<m→1+n≤m (≤refl , ne) = abort (ne refl)
  n<m→1+n≤m (≤1+ n≤m , _) = n≤m→1+n≤1+m n≤m

  n<m→n≤m : ∀{n m} → n < m → n ≤ m
  n<m→n≤m n<m = 1+n≤1+m→n≤m (≤1+ (n<m→1+n≤m n<m))

  <dec : (n m : Nat) → n < m ∨ n == m ∨ m < n
  <dec n m with natEQ n m
  ... | Inl refl = Inr (Inl refl)
  ... | Inr ne   with ≤total {n} {m}
  ... | Inl ≤refl     = abort (ne refl)
  ... | Inl (≤1+ n≤m) = Inl (n≤m→n<1+m n≤m)
  ... | Inr ≤refl     = abort (ne refl)
  ... | Inr (≤1+ m≤n) = Inr (Inr (n≤m→n<1+m m≤n))

  <dec-refl : (n : Nat) → <dec n n == Inr (Inl refl)
  <dec-refl n with <dec n n
  <dec-refl n | Inl (_ , ne)       = abort (ne refl)
  <dec-refl n | Inr (Inl refl)     = refl
  <dec-refl n | Inr (Inr (_ , ne)) = abort (ne refl)

  -- difference theorems

  m-n+n==m : ∀{n m} → (n≤m : n ≤ m) → difference n≤m + n == m
  m-n+n==m ≤refl = refl
  m-n+n==m (≤1+ n≤m) = 1+ap (m-n+n==m n≤m)

  n+m-n==m : ∀{n m} → difference (n≤n+m {n} {m}) == m
  n+m-n==m {n} {m} =
    n+a==m+a→n==m (m-n+n==m {n} n≤n+m · +comm {n})

  diff-proof-irrelevance : ∀{n m} →
                             (n≤m1 n≤m2 : n ≤ m) →
                             difference n≤m1 == difference n≤m2
  diff-proof-irrelevance ≤refl ≤refl = refl
  diff-proof-irrelevance ≤refl (≤1+ n≤m2) = abort (1+n≰n n≤m2)
  diff-proof-irrelevance (≤1+ n≤m1) ≤refl = abort (1+n≰n n≤m1)
  diff-proof-irrelevance (≤1+ n≤m1) (≤1+ n≤m2) = 1+ap (diff-proof-irrelevance n≤m1 n≤m2)

  m-n==1+m-1+n : ∀{n m} →
                   (n≤m : n ≤ m) →
                   (1+n≤1+m : 1+ n ≤ 1+ m) →
                   difference n≤m == difference 1+n≤1+m
  m-n==1+m-1+n {n} {.n} ≤refl ≤refl = refl
  m-n==1+m-1+n {n} {.n} ≤refl (≤1+ 1+n≤n) = abort (1+n≰n 1+n≤n)
  m-n==1+m-1+n {.(1+ _)} {.(1+ _)} (≤1+ 1+m≤m) ≤refl = abort (1+n≰n 1+m≤m)
  m-n==1+m-1+n {n} {.(1+ _)} (≤1+ n≤m) (≤1+ 1+n≤1+m) = 1+ap (m-n==1+m-1+n n≤m 1+n≤1+m)

  m-n==m+s-n+s : ∀{n m s} →
                   (n≤m : n ≤ m) →
                   (n+s≤m+s : n + s ≤ m + s) →
                   difference n≤m == difference n+s≤m+s
  m-n==m+s-n+s {n} {m} {s = Z} n≤m n+s≤m+s
    rewrite n+Z==n {n} | n+Z==n {m}
      = diff-proof-irrelevance n≤m n+s≤m+s
  m-n==m+s-n+s {n} {m} {s = 1+ s} n≤m n+s≤m+s
    rewrite n+1+m==1+n+m {n} {s} | n+1+m==1+n+m {m} {s}
      = (m-n==m+s-n+s n≤m (1+n≤1+m→n≤m n+s≤m+s)) · (m-n==1+m-1+n (1+n≤1+m→n≤m n+s≤m+s) n+s≤m+s)
