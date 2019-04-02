open import Prelude

module Nat where
  data Nat : Set where
    Z : Nat
    1+ : Nat → Nat

  {-# BUILTIN NATURAL Nat #-}

  -- the succ operation is injective
  1+inj : ∀{n m} → 1+ n == 1+ m → n == m
  1+inj refl = refl

  1+ap : ∀{n m} → n == m → 1+ n == 1+ m
  1+ap {n} {.n} refl = refl

  1+ap-cp : ∀{n m} → 1+ n ≠ 1+ m → n ≠ m
  1+ap-cp h1 h2 = h1 (1+ap h2)

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

  _+_ : Nat → Nat → Nat
  Z + m = m
  1+ n + m = 1+ (n + m)

  infixl 60 _+_

  n+Z==n : ∀{n} → n + Z == n
  n+Z==n {Z} = refl
  n+Z==n {1+ n} = 1+ap n+Z==n

  n+1+m==1+n+m : ∀{n m} → n + 1+ m == 1+ (n + m)
  n+1+m==1+n+m {Z} = refl
  n+1+m==1+n+m {1+ n} = 1+ap n+1+m==1+n+m

  +comm : ∀{a b} → a + b == b + a
  +comm {Z} {b} = ! n+Z==n
  +comm {1+ a} {Z} = 1+ap n+Z==n
  +comm {1+ a} {1+ b} with a + 1+ b | b + 1+ a | n+1+m==1+n+m {a} {b} | n+1+m==1+n+m {b} {a}
  +comm {1+ a} {1+ b} | _ | _ | refl | refl = 1+ap (1+ap (+comm {a}))

  +assc : ∀{a b c} → a + b + c == a + (b + c)
  +assc {Z} = refl
  +assc {1+ a} = 1+ap (+assc {a})

  data _≤_ : Nat → Nat → Set where
    ≤refl  : ∀{n} → n ≤ n
    ≤1+    : ∀{n m} → n ≤ m → n ≤ 1+ m

  infix 40 _≤_

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

  <antisym : ∀{n m} → n ≤ m → m ≤ n → n == m
  <antisym {n} {.n} ≤refl m≤n = refl
  <antisym {n} {.(1+ _)} (≤1+ h1) h2 = abort (1+n≰n (≤trans h2 h1))

  _<_ : Nat → Nat → Set
  n < m = n ≤ m ∧ n ≠ m

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

  infix 40 _<_
