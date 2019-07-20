open import Prelude
open import Nat
open import List

module contexts where
  -- helper function
  diff-1 : ∀{n m} → n < m → Nat
  diff-1 n<m = difference (n<m→1+n≤m n<m)

  ---- the core declarations ----
  -- TODO move definitions

  _ctx : Set → Set
  A ctx = List (Nat ∧ A)

  -- nil context
  ∅ : {A : Set} → A ctx
  ∅ = []

  -- singleton context
  ■_ : {A : Set} → (Nat ∧ A) → A ctx
  ■_ (x , a) = (x , a) :: []

  infixr 100 ■_

  -- context extension/insertion - never use _::_
  _,,_ : ∀{A} → A ctx → (Nat ∧ A) → A ctx
  [] ,, (x , a) = ■ (x , a)
  ((hx , ha) :: t) ,, (x , a) with <dec x hx
  ... | Inl x<hx       = (x , a) :: ((diff-1 x<hx , ha) :: t)
  ... | Inr (Inl refl) = (x , a) :: t
  ... | Inr (Inr hx<x) = (hx , ha) :: (t ,, (diff-1 hx<x , a))

  infixl 10 _,,_

  -- membership, or presence, in a context
  data _∈_ : {A : Set} (p : Nat ∧ A) → (Γ : A ctx) → Set where
    InH : {A : Set} {Γ : A ctx} {x : Nat} {a : A} →
           (x , a) ∈ ((x , a) :: Γ)
    InT : {A : Set} {Γ : A ctx} {x s : Nat} {a a' : A} →
           (x , a) ∈ Γ →
           ((x + 1+ s , a)) ∈ ((s , a') :: Γ)

  -- the domain of a context
  dom : {A : Set} → A ctx → Nat → Set
  dom {A} Γ x = Σ[ a ∈ A ] ((x , a) ∈ Γ)

  -- apartness for contexts
  _#_ : {A : Set} (n : Nat) → (Γ : A ctx) → Set
  x # Γ = dom Γ x → ⊥

  _##_ : {A : Set} → A ctx → A ctx → Set
  Γ1 ## Γ2 = (x : Nat) → dom Γ1 x → x # Γ2

  -- TODO theorems and explanation
  ctxmap : {A B : Set} → (A → B) → A ctx → B ctx
  ctxmap f Γ = map (λ {(hx , ha) → (hx , f ha)}) Γ

  -- TODO theorems
  -- returns a list of the values stored in the context
  ctx⇒values : {A : Set} → A ctx → List A

  -- TODO theorems and explanation
  list⇒ctx : {A : Set} → List (Nat ∧ A) → (List A) ctx

  -- TODO theorems
  -- a ∪ b is the union of a and b, with mappings in b overriding those in a
  _∪_ : {A : Set} → A ctx → A ctx → A ctx

  infixl 50 _∪_

  -- The primary way to test membership is to use _∈_,
  -- but this can be used in cases where using _∈_
  -- would be too verbose or awkward.
  -- The lookup theorems prove that they are compatible
  _⦃⦃_⦄⦄ : {A : Set} → A ctx → Nat → Maybe A
  [] ⦃⦃ x ⦄⦄ = None
  ((hx , ha) :: t) ⦃⦃ x ⦄⦄ with <dec x hx
  ... | Inl x<hx       = None
  ... | Inr (Inl refl) = Some ha
  ... | Inr (Inr hx<x) = t ⦃⦃ diff-1 hx<x ⦄⦄

  ---- some definitions ----

  -- TODO maybe define ctx⇒list then refactor this
  union' : {A : Set} → A ctx → A ctx → Nat → A ctx
  union' Γ1 [] _ = Γ1
  union' Γ1 ((hx , ha) :: Γ2) offset
    = union' (Γ1 ,, (hx + offset , ha)) Γ2 (offset + 1+ hx)

  Γ1 ∪ Γ2 = union' Γ1 Γ2 0

  ---- lemmas ----

  undiff-1 : (x s : Nat) → (x<s+1+x : x < s + 1+ x) → s == diff-1 x<s+1+x
  undiff-1 x s x<s+1+x
    rewrite n+1+m==1+n+m {s} {x} | ! (m-n==1+m-1+n n≤m+n (n<m→1+n≤m x<s+1+x)) | +comm {s} {x}
      = ! (n+m-n==m n≤n+m)

  too-small : {A : Set} {Γ : A ctx} {xl xb : Nat} {a : A} →
               xl < xb →
               dom ((xb , a) :: Γ) xl →
               ⊥
  too-small (_ , ne) (_ , InH) = ne refl
  too-small (x+1+xb≤xb , x+1+xb==xb) (_ , InT _) =
    x+1+xb==xb (≤antisym x+1+xb≤xb (≤trans (≤1+ ≤refl) n≤m+n))

  all-not-none : {A : Set} {Γ : A ctx} {x : Nat} {a : A} →
                  None ≠ (((x , a) :: Γ) ⦃⦃ x ⦄⦄)
  all-not-none {x = x} rewrite <dec-refl x = λ ()

  all-bindings-==-rec-eq : {A : Set} {Γ1 Γ2 : A ctx} {x : Nat} {a : A} →
                            ((x' : Nat) → ((x , a) :: Γ1) ⦃⦃ x' ⦄⦄ == ((x , a) :: Γ2) ⦃⦃ x' ⦄⦄) →
                            ((x' : Nat) → Γ1 ⦃⦃ x' ⦄⦄ == Γ2 ⦃⦃ x' ⦄⦄)
  all-bindings-==-rec-eq {x = x} h x'
    with h (x' + 1+ x)
  ... | eq
    with <dec (x' + 1+ x) x
  ... | Inl x'+1+x<x
          = abort (<antisym x'+1+x<x (n<m→n<s+m n<1+n))
  ... | Inr (Inl x'+1+x==x)
          = abort ((flip n≠n+1+m) (n+1+m==1+n+m · (+comm {1+ x} · x'+1+x==x)))
  ... | Inr (Inr x<x'+1+x)
          rewrite ! (undiff-1 x x' x<x'+1+x) = eq

  all-bindings-==-rec : {A : Set} {Γ1 Γ2 : A ctx} {x1 x2 : Nat} {a1 a2 : A} →
                         ((x : Nat) → ((x1 , a1) :: Γ1) ⦃⦃ x ⦄⦄ == ((x2 , a2) :: Γ2) ⦃⦃ x ⦄⦄) →
                         ((x : Nat) → Γ1 ⦃⦃ x ⦄⦄ == Γ2 ⦃⦃ x ⦄⦄)
  all-bindings-==-rec {x1 = x1} {x2} h x
    with h x1 | h x2
  ... | eq1 | eq2
    rewrite <dec-refl x1 | <dec-refl x2
    with <dec x1 x2 | <dec x2 x1
  ... | Inl _ | _
          = abort (somenotnone eq1)
  ... | Inr _ | Inl _
          = abort (somenotnone (! eq2))
  ... | Inr (Inl refl) | Inr (Inl refl)
          rewrite someinj eq1 | someinj eq2
            = all-bindings-==-rec-eq h x
  ... | Inr (Inl refl) | Inr (Inr x2<x2)
          = abort (<antirefl x2<x2)
  ... | Inr (Inr x2<x2) | Inr (Inl refl)
          = abort (<antirefl x2<x2)
  ... | Inr (Inr x2<x1) | Inr (Inr x1<x2)
          = abort (<antisym x1<x2 x2<x1)

  ---- core theorems ----

  -- lookup is decidable
  lookup-dec : {A : Set} (Γ : A ctx) (x : Nat) →
                Σ[ a ∈ A ] (Γ ⦃⦃ x ⦄⦄ == Some a) ∨ Γ ⦃⦃ x ⦄⦄ == None
  lookup-dec Γ x
    with Γ ⦃⦃ x ⦄⦄
  ... | Some a = Inl (a , refl)
  ... | None   = Inr refl

  -- The next two theorems show that lookup (_⦃⦃_⦄⦄) is consistent with membership (_∈_)
  lookup-cons-1 : {A : Set} {Γ : A ctx} {x : Nat} {a : A} →
                   Γ ⦃⦃ x ⦄⦄ == Some a →
                   (x , a) ∈ Γ
  lookup-cons-1 {Γ = []} ()
  lookup-cons-1 {Γ = (hx , ha) :: t} {x} h
    with <dec x hx
  lookup-cons-1 {_} {(hx , ha) :: t} {x} ()        | Inl _
  lookup-cons-1 {_} {(hx , ha) :: t} {.hx} refl    | Inr (Inl refl) = InH
  lookup-cons-1 {_} {(hx , ha) :: t} {x} {a = a} h | Inr (Inr hx<x)
    = tr
        (λ y → (y , a) ∈ ((hx , ha) :: t))
        (m-n+n==m (n<m→1+n≤m hx<x))
        (InT (lookup-cons-1 {Γ = t} h))

  lookup-cons-2 : {A : Set} {Γ : A ctx} {x : Nat} {a : A} →
                   (x , a) ∈ Γ →
                   Γ ⦃⦃ x ⦄⦄ == Some a
  lookup-cons-2 {x = x} InH rewrite <dec-refl x = refl
  lookup-cons-2 (InT {Γ = Γ} {x = x} {s} {a} x∈Γ)
    with <dec (x + 1+ s) s
  ... | Inl x+1+s<s        = abort (<antisym x+1+s<s (n<m→n<s+m n<1+n))
  ... | Inr (Inl x+1+s==s) = abort ((flip n≠n+1+m) (n+1+m==1+n+m · (+comm {1+ s} · x+1+s==s)))
  ... | Inr (Inr s<x+1+s)
    with lookup-cons-2 x∈Γ
  ... | h rewrite ! (undiff-1 s x s<x+1+s) = h

  -- membership (_∈_) respects insertion (_,,_)
  x,a∈Γ,,x,a : {A : Set} {Γ : A ctx} {x : Nat} {a : A} →
                (x , a) ∈ (Γ ,, (x , a))
  x,a∈Γ,,x,a {Γ = []} {x} {a} = InH
  x,a∈Γ,,x,a {_} {(hx , ha) :: t} {x} {a}
    with <dec x hx
  ... | Inl _          = InH
  ... | Inr (Inl refl) = InH
  ... | Inr (Inr hx<x) =
          tr
            (λ y → (y , a) ∈ ((hx , ha) :: (t ,, (diff-1 hx<x , a))))
            (m-n+n==m (n<m→1+n≤m hx<x))
            (InT (x,a∈Γ,,x,a {Γ = t} {diff-1 hx<x} {a}))

  -- insertion can't generate spurious membership
  x∈Γ+→x∈Γ : {A : Set} {Γ : A ctx} {x x' : Nat} {a a' : A} →
                x ≠ x' →
                (x , a) ∈ (Γ ,, (x' , a')) →
                (x , a) ∈ Γ
  x∈Γ+→x∈Γ {Γ = []} x≠x' InH = abort (x≠x' refl)
  x∈Γ+→x∈Γ {Γ = []} x≠x' (InT ())
  x∈Γ+→x∈Γ {Γ = (hx , ha) :: t} {x' = x'} x≠x' x∈Γ+
    with <dec x' hx
  x∈Γ+→x∈Γ {_} {(hx , ha) :: t} {x' = x'} x≠x' InH | Inl x'<hx = abort (x≠x' refl)
  x∈Γ+→x∈Γ {_} {(hx , ha) :: t} {x' = x'} x≠x' (InT InH) | Inl x'<hx
    rewrite m-n+n==m (n<m→1+n≤m x'<hx) = InH
  x∈Γ+→x∈Γ {_} {(hx , ha) :: t} {x' = x'} x≠x' (InT (InT {x = x} x∈Γ+)) | Inl x'<hx
    rewrite +assc {x} {1+ (diff-1 x'<hx)} {1+ x'} | m-n+n==m (n<m→1+n≤m x'<hx)
      = InT x∈Γ+
  x∈Γ+→x∈Γ {_} {(hx , ha) :: t} {x' = .hx} x≠x' InH | Inr (Inl refl) = abort (x≠x' refl)
  x∈Γ+→x∈Γ {_} {(hx , ha) :: t} {x' = .hx} x≠x' (InT x∈Γ+) | Inr (Inl refl) = InT x∈Γ+
  x∈Γ+→x∈Γ {_} {(hx , ha) :: t} {x' = x'} x≠x' InH | Inr (Inr hx<x') = InH
  x∈Γ+→x∈Γ {_} {(hx , ha) :: t} {x' = x'} x≠x' (InT x∈Γ+) | Inr (Inr hx<x')
    = InT (x∈Γ+→x∈Γ (λ where refl → x≠x' (m-n+n==m (n<m→1+n≤m hx<x'))) x∈Γ+)

  -- insertion respects membership
  x∈Γ→x∈Γ+ : {A : Set} {Γ : A ctx} {x x' : Nat} {a a' : A} →
                x ≠ x' →
                (x , a) ∈ Γ →
                (x , a) ∈ (Γ ,, (x' , a'))
  x∈Γ→x∈Γ+ {x = x} {x'} {a} {a'} x≠x' (InH {Γ = Γ'})
    with <dec x' x
  ... | Inl x'<x
          = tr
              (λ y → (y , a) ∈ ((x' , a') :: ((diff-1 x'<x , a) :: Γ')))
              (m-n+n==m (n<m→1+n≤m x'<x))
              (InT InH)
  ... | Inr (Inl refl) = abort (x≠x' refl)
  ... | Inr (Inr x<x') = InH
  x∈Γ→x∈Γ+ {x = .(_ + 1+ _)} {x'} {a} {a'} x≠x' (InT {Γ = Γ} {x} {s} {a' = a''} x∈Γ)
    with <dec x' s
  ... | Inl x'<s
          = tr
              (λ y → (y , a) ∈ ((x' , a') :: ((diff-1 x'<s , a'') :: Γ)))
              ((+assc {b = 1+ (diff-1 x'<s)}) · (ap1 (_+_ x) (1+ap (m-n+n==m (n<m→1+n≤m x'<s)))))
              (InT (InT x∈Γ))
  ... | Inr (Inl refl) = InT x∈Γ
  ... | Inr (Inr s<x') =
          InT (x∈Γ→x∈Γ+ (λ where refl → x≠x' (m-n+n==m (n<m→1+n≤m s<x'))) x∈Γ)

  -- Decidability of membership
  -- This also packages up an appeal to context membership into a form that
  -- lets us retain more information
  ctxindirect : {A : Set} (Γ : A ctx) (x : Nat) → dom Γ x ∨ x # Γ
  ctxindirect [] x = Inr (λ ())
  ctxindirect ((hx , ha) :: t) x
    with <dec x hx
  ... | Inl x<hx       = Inr (too-small x<hx)
  ... | Inr (Inl refl) = Inl (ha , InH)
  ... | Inr (Inr hx<x)
    with ctxindirect t (diff-1 hx<x)
  ctxindirect ((hx , ha) :: t) x | Inr (Inr hx<x) | Inl (a , rec) =
    Inl (a , tr
               (λ y → (y , a) ∈ ((hx , ha) :: t))
               (m-n+n==m (n<m→1+n≤m hx<x))
               (InT rec))
  ctxindirect {A} ((hx , ha) :: t) x | Inr (Inr hx<x) | Inr dne =
    Inr x∉Γ
    where
      x∉Γ : Σ[ a ∈ A ] ((x , a) ∈ ((hx , ha) :: t)) → ⊥
      x∉Γ (_ , x∈Γ) with x∈Γ
      ... | InH = (π2 hx<x) refl
      ... | InT {x = s} x-hx-1∈t
        rewrite ! (undiff-1 hx s hx<x) = dne (_ , x-hx-1∈t)

  -- contexts give at most one binding for each variable
  ctxunicity : {A : Set} {Γ : A ctx} {x : Nat} {a a' : A} →
                 (x , a) ∈ Γ →
                 (x , a') ∈ Γ →
                 a == a'
  ctxunicity ah a'h
    with lookup-cons-2 ah | lookup-cons-2 a'h
  ... | ah' | a'h' = someinj (! ah' · a'h')

  -- everything is apart from the nil context
  x#∅ : {A : Set} {x : Nat} → _#_ {A} x ∅
  x#∅ (_ , ())

  -- if an index is in the domain of a singleton context, it's the only
  -- index in the context
  lem-dom-eq : {A : Set} {a : A} {n m : Nat} →
                 dom (■ (m , a)) n →
                 n == m
  lem-dom-eq (_ , InH) = refl
  lem-dom-eq (_ , InT ())

  -- If two contexts are semantically equivalent
  -- (i.e. they represent the same mapping from ids to values),
  -- then they are physically equal as judged by _==_
  ctx-==-eqv : {A : Set} {Γ1 Γ2 : A ctx} →
                ((x : Nat) → Γ1 ⦃⦃ x ⦄⦄ == Γ2 ⦃⦃ x ⦄⦄) →
                Γ1 == Γ2
  ctx-==-eqv {Γ1 = []} {[]} all-bindings-== = refl
  ctx-==-eqv {Γ1 = []} {(hx2 , ha2) :: t2} all-bindings-==
    = abort (all-not-none {Γ = t2} {x = hx2} (all-bindings-== hx2))
  ctx-==-eqv {Γ1 = (hx1 , ha1) :: t1} {[]} all-bindings-==
    = abort (all-not-none {Γ = t1} {x = hx1} (! (all-bindings-== hx1)))
  ctx-==-eqv {Γ1 = (hx1 , ha1) :: t1} {(hx2 , ha2) :: t2} all-bindings-==
    rewrite ctx-==-eqv {Γ1 = t1} {t2} (all-bindings-==-rec all-bindings-==)
    with all-bindings-== hx1 | all-bindings-== hx2
  ... | ha1== | ha2== rewrite <dec-refl hx1 | <dec-refl hx2
    with <dec hx1 hx2 | <dec hx2 hx1
  ... | Inl hx1<hx2 | _
          = abort (somenotnone ha1==)
  ... | Inr (Inl refl) | Inl hx2<hx1
          = abort (somenotnone (! ha2==))
  ... | Inr (Inr hx2<hx1) | Inl hx2<'hx1
          = abort (somenotnone (! ha2==))
  ... | Inr (Inl refl) | Inr _
          rewrite someinj ha1== = refl
  ... | Inr (Inr hx2<hx1) | Inr (Inl refl)
          rewrite someinj ha2== = refl
  ... | Inr (Inr hx2<hx1) | Inr (Inr hx1<hx2)
          = abort (<antisym hx1<hx2 hx2<hx1)

  -- equality of contexts is decidable
  ctx-==-dec : {A : Set}
                (Γ1 Γ2 : A ctx) →
                ((a1 a2 : A) → a1 == a2 ∨ a1 ≠ a2) →
                Γ1 == Γ2 ∨ Γ1 ≠ Γ2
  ctx-==-dec [] [] _ = Inl refl
  ctx-==-dec [] (_ :: _) _ = Inr (λ ())
  ctx-==-dec (_ :: _) [] _ = Inr (λ ())
  ctx-==-dec ((hx1 , ha1) :: t1) ((hx2 , ha2) :: t2) A==dec
    with natEQ hx1 hx2 | A==dec ha1 ha2 | ctx-==-dec t1 t2 A==dec
  ... | Inl refl | Inl refl | Inl refl = Inl refl
  ... | Inl refl | Inl refl | Inr ne   = Inr λ where refl → ne refl
  ... | Inl refl | Inr ne   | _        = Inr λ where refl → ne refl
  ... | Inr ne   | _        | _        = Inr λ where refl → ne refl

  -- A useful way to destruct context membership. Never destruct a context via _::_
  ctx-split : {A : Set} {Γ : A ctx} {n m : Nat} {an am : A} →
                (n , an) ∈ (Γ ,, (m , am)) →
                (n ≠ m ∧ (n , an) ∈ Γ) ∨ (n == m ∧ an == am)
  ctx-split {Γ = Γ} {n} {m} {an} {am} n∈Γ+
    with natEQ n m
  ... | Inl refl = Inr (refl , ctxunicity n∈Γ+ (x,a∈Γ,,x,a {Γ = Γ}))
  ... | Inr n≠m  = Inl (n≠m , x∈Γ+→x∈Γ n≠m n∈Γ+)

  -- I'd say "God dammit agda" but AFAICT Coq is terrible about this as well
  lemma-bullshit : {A : Set} (Γ' : A ctx) (a : A) (n m : Nat) →
                    Σ[ Γ ∈ A ctx ] (Γ == (n + 1+ m , a) :: Γ')
  lemma-bullshit Γ' a n m = ((n + 1+ m , a) :: Γ') , refl

  -- Allows the elimination of contexts. Never destruct a context via _::_
  ctx-elim : {A : Set} {Γ : A ctx} →
              Γ == ∅
                ∨
              Σ[ n ∈ Nat ] Σ[ a ∈ A ] Σ[ Γ' ∈ A ctx ]
                 (Γ == Γ' ,, (n , a) ∧ n # Γ')
  ctx-elim {Γ = []}            = Inl refl
  ctx-elim {Γ = (n , a) :: []} = Inr (_ , _ , _ , refl , x#∅)
  ctx-elim {Γ = (n , a) :: ((m , a2) :: Γ'')}
    with lemma-bullshit Γ'' a2 m n
  ... | Γ' , eq
    = Inr (n , a , Γ' , eqP , not-dom)
      where
        eqP : (n , a) :: ((m , a2) :: Γ'') == Γ' ,, (n , a)
        eqP rewrite eq with <dec n (m + 1+ n)
        ... | Inl n<m+1+n
          rewrite ! (undiff-1 n m n<m+1+n) = refl
        ... | Inr (Inl n==m+1+n)
          = abort (n≠n+1+m (n==m+1+n · (n+1+m==1+n+m · +comm {1+ m})))
        ... | Inr (Inr m+1+n<n)
          = abort (<antisym m+1+n<n (n<m→n<s+m n<1+n))
        not-dom : dom Γ' n → ⊥
        not-dom rewrite eq = λ n∈Γ' →
          too-small (n<m→n<s+m n<1+n) n∈Γ'

  -- When using ctx-elim, this theorem is useful for establishing termination
  ctx-decreasing : {A : Set} {Γ : A ctx} {n : Nat} {a : A} →
                    n # Γ →
                    ∥ Γ ,, (n , a) ∥ == 1+ ∥ Γ ∥
  ctx-decreasing {Γ = []} n#Γ = refl
  ctx-decreasing {Γ = (n' , a') :: Γ} {n} n#Γ
    with <dec n n'
  ... | Inl n<n'       = refl
  ... | Inr (Inl refl) = abort (n#Γ (_ , InH))
  ... | Inr (Inr n'<n)
    = 1+ap (ctx-decreasing λ {(a , diff∈Γ) →
        n#Γ (a , tr
                   (λ y → (y , a) ∈ ((n' , a') :: Γ))
                   (m-n+n==m (n<m→1+n≤m n'<n))
                   (InT diff∈Γ))})

  ---- contrapositives of some previous theorems ----

  lem-neq-apart : {A : Set} {a : A} {n m : Nat} →
                    n ≠ m →
                    n # (■ (m , a))
  lem-neq-apart n≠m h = n≠m (lem-dom-eq h)

  x#Γ→x#Γ+ : {A : Set} {Γ : A ctx} {x x' : Nat} {a' : A} →
               x ≠ x' →
               x # Γ →
               x # (Γ ,, (x' , a'))
  x#Γ→x#Γ+ {Γ = Γ} {x} {x'} {a'} x≠x' x#Γ
    with ctxindirect (Γ ,, (x' , a')) x
  ... | Inl (_ , x∈Γ+) = abort (x#Γ (_ , x∈Γ+→x∈Γ x≠x' x∈Γ+))
  ... | Inr x#Γ+       = x#Γ+

  x#Γ+→x#Γ : {A : Set} {Γ : A ctx} {x x' : Nat} {a' : A} →
               x # (Γ ,, (x' , a')) →
               x # Γ
  x#Γ+→x#Γ {Γ = Γ} {x} {x'} {a'} x#Γ+
    with ctxindirect Γ x
  ... | Inr x#Γ       = x#Γ
  ... | Inl (_ , x∈Γ)
    with natEQ x x'
  ... | Inl refl = abort (x#Γ+ (_ , x,a∈Γ,,x,a {Γ = Γ}))
  ... | Inr x≠x' = abort (x#Γ+ (_ , x∈Γ→x∈Γ+ x≠x' x∈Γ))

  lookup-cp-1 : {A : Set} {Γ : A ctx} {x : Nat} →
                 x # Γ →
                 Γ ⦃⦃ x ⦄⦄ == None
  lookup-cp-1 {Γ = Γ} {x} x#Γ
    with lookup-dec Γ x
  ... | Inl (_ , x∈Γ) = abort (x#Γ (_ , (lookup-cons-1 x∈Γ)))
  ... | Inr x#'Γ      = x#'Γ

  lookup-cp-2 : {A : Set} {Γ : A ctx} {x : Nat} →
                 Γ ⦃⦃ x ⦄⦄ == None →
                 x # Γ
  lookup-cp-2 {Γ = Γ} {x} x#Γ
    with ctxindirect Γ x
  ... | Inl (_ , x∈Γ) = abort (somenotnone ((! (lookup-cons-2 x∈Γ)) · x#Γ))
  ... | Inr x#'Γ      = x#'Γ

  ---- contraction and exchange ----

  -- TODO these proofs could use refactoring -
  -- contraction should probably make use of ctx-==-dec and
  -- exchange is way too long and repetitive

  contraction : {A : Set} {Γ : A ctx} {x : Nat} {a a' : A} →
                 Γ ,, (x , a') ,, (x , a) == Γ ,, (x , a)
  contraction {Γ = []} {x} rewrite <dec-refl x = refl
  contraction {Γ = (hx , ha) :: t} {x} {a} {a'}
    with <dec x hx
  ... | Inl _          rewrite <dec-refl x  = refl
  ... | Inr (Inl refl) rewrite <dec-refl hx = refl
  ... | Inr (Inr hx<x)
    with <dec x hx
  ... | Inl x<hx        = abort (<antisym x<hx hx<x)
  ... | Inr (Inl refl)  = abort (<antirefl hx<x)
  ... | Inr (Inr hx<'x)
    rewrite diff-proof-irrelevance (n<m→1+n≤m hx<x) (n<m→1+n≤m hx<'x)
          | contraction {Γ = t} {diff-1 hx<'x} {a} {a'}
    = refl

  exchange : {A : Set} {Γ : A ctx} {x1 x2 : Nat} {a1 a2 : A} →
              x1 ≠ x2 →
              Γ ,, (x1 , a1) ,, (x2 , a2) == Γ ,, (x2 , a2) ,, (x1 , a1)
  exchange {A} {Γ} {x1} {x2} {a1} {a2} x1≠x2
    = ctx-==-eqv fun
      where
        fun : (x : Nat) →
               (Γ ,, (x1 , a1) ,, (x2 , a2)) ⦃⦃ x ⦄⦄ ==
               (Γ ,, (x2 , a2) ,, (x1 , a1)) ⦃⦃ x ⦄⦄
        fun x
          with natEQ x x1 | natEQ x x2 | ctxindirect Γ x
        fun x  | Inl refl | Inl refl | _
          = abort (x1≠x2 refl)
        fun x1 | Inl refl | Inr x≠x2 | Inl (_ , x1∈Γ)
          with x,a∈Γ,,x,a {Γ = Γ} {x1} {a1}
        ... | x∈Γ+1
          with x∈Γ→x∈Γ+ {a' = a2} x≠x2 x∈Γ+1 | x,a∈Γ,,x,a {Γ = Γ ,, (x2 , a2)} {x1} {a1}
        ... | x∈Γ++1 | x∈Γ++2
          rewrite lookup-cons-2 x∈Γ++1 | lookup-cons-2 x∈Γ++2 = refl
        fun x1 | Inl refl | Inr x≠x2 | Inr x1#Γ
          with x,a∈Γ,,x,a {Γ = Γ} {x1} {a1}
        ... | x∈Γ+1
          with x∈Γ→x∈Γ+ {a' = a2} x≠x2 x∈Γ+1 | x,a∈Γ,,x,a {Γ = Γ ,, (x2 , a2)} {x1} {a1}
        ... | x∈Γ++1 | x∈Γ++2
          rewrite lookup-cons-2 x∈Γ++1 | lookup-cons-2 x∈Γ++2 = refl
        fun x2 | Inr x≠x1 | Inl refl | Inl (_ , x2∈Γ)
          with x,a∈Γ,,x,a {Γ = Γ} {x2} {a2}
        ... | x∈Γ+2
          with x∈Γ→x∈Γ+ {a' = a1} x≠x1 x∈Γ+2 | x,a∈Γ,,x,a {Γ = Γ ,, (x1 , a1)} {x2} {a2}
        ... | x∈Γ++1 | x∈Γ++2
          rewrite lookup-cons-2 x∈Γ++1 | lookup-cons-2 x∈Γ++2 = refl
        fun x2 | Inr x≠x1 | Inl refl | Inr x2#Γ
          with x,a∈Γ,,x,a {Γ = Γ} {x2} {a2}
        ... | x∈Γ+2
          with x∈Γ→x∈Γ+ {a' = a1} x≠x1 x∈Γ+2 | x,a∈Γ,,x,a {Γ = Γ ,, (x1 , a1)} {x2} {a2}
        ... | x∈Γ++1 | x∈Γ++2
          rewrite lookup-cons-2 x∈Γ++1 | lookup-cons-2 x∈Γ++2 = refl
        fun x  | Inr x≠x1 | Inr x≠x2 | Inl (_ , x∈Γ)
          with x∈Γ→x∈Γ+ {a' = a1} x≠x1 x∈Γ   | x∈Γ→x∈Γ+ {a' = a2} x≠x2 x∈Γ
        ... | x∈Γ+1  | x∈Γ+2
          with x∈Γ→x∈Γ+ {a' = a2} x≠x2 x∈Γ+1 | x∈Γ→x∈Γ+ {a' = a1} x≠x1 x∈Γ+2
        ... | x∈Γ++1 | x∈Γ++2
          rewrite lookup-cons-2 x∈Γ++1 | lookup-cons-2 x∈Γ++2 = refl
        fun x  | Inr x≠x1 | Inr x≠x2 | Inr x#Γ
          with x#Γ→x#Γ+ {a' = a1} x≠x1 x#Γ   | x#Γ→x#Γ+ {a' = a2} x≠x2 x#Γ
        ... | x#Γ+1  | x#Γ+2
          with x#Γ→x#Γ+ {a' = a2} x≠x2 x#Γ+1 | x#Γ→x#Γ+ {a' = a1} x≠x1 x#Γ+2
        ... | x#Γ++1 | x#Γ++2
          rewrite lookup-cp-1 x#Γ++1 | lookup-cp-1 x#Γ++2 = refl

  ---- remaining function definitions ----

  -- TODO redefine using foldl
  list⇒ctx [] = ∅
  list⇒ctx ((n , a) :: l)
    with list⇒ctx l
  ... | l-ctx
    with ctxindirect l-ctx n
  ... | Inl (as , n∈l-ctx)
          = l-ctx ,, (n , a :: as)
  ... | Inr n#rest-ctx
          = l-ctx ,, (n , a :: [])

  ctx⇒values = map π2
