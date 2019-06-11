open import Prelude
open import Nat
open import Agda.Primitive using (Level; lzero; lsuc) renaming (_⊔_ to lmax)

module List where

  -- definitions

  data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A

  _++_ : {A : Set} → List A → List A → List A
  [] ++ l₂ = l₂
  (h :: l₁) ++ l₂ = h :: (l₁ ++ l₂)

  infixl 50 _++_

  ∥_∥ : {A : Set} → List A → Nat
  ∥ [] ∥ = Z
  ∥ a :: as ∥ = 1+ ∥ as ∥

  _⟦_⟧ : {A : Set} → List A → Nat → Maybe A
  [] ⟦ i ⟧ = None
  (a :: as) ⟦ Z ⟧ = Some a
  (a :: as) ⟦ 1+ i ⟧ = as ⟦ i ⟧

  map : {A B : Set} → (A → B) → List A → List B
  map f [] = []
  map f (a :: as) = f a :: map f as

  foldl : {A B : Set} → (B → A → B) → B → List A → B
  foldl f b [] = b
  foldl f b (a :: as) = foldl f (f b a) as

  concat : {A : Set} → List (List A) → List A
  concat [] = []
  concat (l1 :: rest) = l1 ++ (concat rest)

  -- theorems

  list-==-dec :  {A : Set} →
                 (l1 l2 : List A) →
                 ((a1 a2 : A) → a1 == a2 ∨ a1 ≠ a2) →
                 l1 == l2 ∨ l1 ≠ l2
  list-==-dec [] [] A-==-dec       = Inl refl
  list-==-dec [] (_ :: _) A-==-dec = Inr (λ ())
  list-==-dec (_ :: _) [] A-==-dec = Inr (λ ())
  list-==-dec (h1 :: t1) (h2 :: t2) A-==-dec
    with A-==-dec h1 h2
  ... | Inr ne = Inr (λ where refl → ne refl)
  ... | Inl refl
    with list-==-dec t1 t2 A-==-dec
  ... | Inr ne = Inr (λ where refl → ne refl)
  ... | Inl refl = Inl refl

  -- if the items of two lists are equal, then the lists are equal
  ==-per-elem : {A : Set} → {l1 l2 : List A} →
                 ((i : Nat) → l1 ⟦ i ⟧ == l2 ⟦ i ⟧) →
                 l1 == l2
  ==-per-elem {l1 = []} {[]} items== = refl
  ==-per-elem {l1 = []} {h2 :: t2} items== = abort (somenotnone (! (items== Z)))
  ==-per-elem {l1 = h1 :: t1} {[]} items== = abort (somenotnone (items== Z))
  ==-per-elem {l1 = h1 :: t1} {h2 :: t2} items==
    rewrite someinj (items== Z) | ==-per-elem {l1 = t1} {t2} (λ i → items== (1+ i))
      = refl

  -- _++_ theorem
  ++assc : ∀{A a1 a2 a3} → (_++_ {A} a1 a2) ++ a3 == a1 ++ (a2 ++ a3)
  ++assc {A} {[]} {a2} {a3} = refl
  ++assc {A} {x :: a1} {a2} {a3} with a1 ++ a2 ++ a3 | ++assc {A} {a1} {a2} {a3}
  ++assc {A} {x :: a1} {a2} {a3} | _ | refl = refl

  -- ∥_∥ theorem
  ∥-++-comm : ∀{A a1 a2} → ∥ a1 ∥ + (∥_∥ {A} a2) == ∥ a1 ++ a2 ∥
  ∥-++-comm {A} {[]} {a2} = refl
  ∥-++-comm {A} {a :: a1} {a2} = 1+ap (∥-++-comm {A} {a1})

  -- _⟦_⟧ and ++ theorem
  ⦇l1++[a]++l2⦈⟦∥l1∥⟧==a : {A : Set} {l1 l2 : List A} {a : A} →
                             (h : ∥ l1 ∥ < ∥ l1 ++ (a :: []) ++ l2 ∥) →
                             ((l1 ++ (a :: []) ++ l2) ⟦ ∥ l1 ∥ ⟧ == Some a)
  ⦇l1++[a]++l2⦈⟦∥l1∥⟧==a {l1 = []} h = refl
  ⦇l1++[a]++l2⦈⟦∥l1∥⟧==a {l1 = a1 :: l1rest} {l2} {a} h = ⦇l1++[a]++l2⦈⟦∥l1∥⟧==a {l1 = l1rest} {l2} {a} (1+n<1+m→n<m h)

  -- packaging of list indexing results
  list-index-dec : {A : Set} (l : List A) (i : Nat) →
                    l ⟦ i ⟧ == None ∨ Σ[ a ∈ A ] (l ⟦ i ⟧ == Some a)
  list-index-dec l i
    with l ⟦ i ⟧
  ... | None   = Inl refl
  ... | Some a = Inr (a , refl)

  -- theorems characterizing the partiality of list indexing
  list-index-some : {A : Set} {l : List A} {i : Nat} →
                     i < ∥ l ∥ →
                     Σ[ a ∈ A ] (l ⟦ i ⟧ == Some a)
  list-index-some {l = []}      {Z}    i<∥l∥ = abort (n≮0 i<∥l∥)
  list-index-some {l = a :: as} {Z}    i<∥l∥ = _ , refl
  list-index-some {l = a :: as} {1+ i} i<∥l∥ = list-index-some (1+n<1+m→n<m i<∥l∥)

  list-index-none : {A : Set} {l : List A} {i : Nat} →
                     ∥ l ∥ ≤ i →
                     l ⟦ i ⟧ == None
  list-index-none {l = []}             i≥∥l∥ = refl
  list-index-none {l = a :: as} {1+ i} i≥∥l∥ = list-index-none (1+n≤1+m→n≤m i≥∥l∥)

  list-index-some-conv : {A : Set} {l : List A} {i : Nat} {a : A} →
                          l ⟦ i ⟧ == Some a →
                          i < ∥ l ∥
  list-index-some-conv {l = l} {i} i≥∥l∥
    with <dec ∥ l ∥ i
  ... | Inr (Inr i<∥l∥) = i<∥l∥
  ... | Inr (Inl refl)
    rewrite list-index-none {l = l} {∥ l ∥} ≤refl
      = abort (somenotnone (! i≥∥l∥))
  ... | Inl ∥l∥<i
    rewrite list-index-none (n<m→n≤m ∥l∥<i)
      = abort (somenotnone (! i≥∥l∥))

  list-index-none-conv : {A : Set} {l : List A} {i : Nat} →
                          l ⟦ i ⟧ == None →
                          ∥ l ∥ ≤ i
  list-index-none-conv {l = l} {i} i≥∥l∥
    with <dec ∥ l ∥ i
  ... | Inl ∥l∥<i       = n<m→n≤m ∥l∥<i
  ... | Inr (Inl refl) = ≤refl
  ... | Inr (Inr i<∥l∥)
    with list-index-some i<∥l∥
  ... | _ , i≱∥l∥ rewrite i≥∥l∥ = abort (somenotnone (! i≱∥l∥))

  ∥l1∥==∥l2∥→l1[i]→l2[i] : {A B : Set} {la : List A} {lb : List B} {i : Nat} {a : A} →
                             ∥ la ∥ == ∥ lb ∥ →
                             la ⟦ i ⟧ == Some a →
                             Σ[ b ∈ B ] (lb ⟦ i ⟧ == Some b)
  ∥l1∥==∥l2∥→l1[i]→l2[i] {i = i} ∥la∥==∥lb∥ la[i]==a
    = list-index-some (tr (λ y → i < y) ∥la∥==∥lb∥ (list-index-some-conv la[i]==a))

  ∥l1∥==∥l2∥→¬l1[i]→¬l2[i] : {A B : Set} {la : List A} {lb : List B} {i : Nat} →
                                ∥ la ∥ == ∥ lb ∥ →
                                la ⟦ i ⟧ == None →
                                lb ⟦ i ⟧ == None
  ∥l1∥==∥l2∥→¬l1[i]→¬l2[i] {i = i} ∥la∥==∥lb∥ la[i]==None
    = list-index-none (tr (λ y → y ≤ i) ∥la∥==∥lb∥ (list-index-none-conv la[i]==None))

  -- map theorem
  map-++-comm : ∀{A B f a b} → map f a ++ map f b == map {A} {B} f (a ++ b)
  map-++-comm {a = []} = refl
  map-++-comm {A} {B} {f} {h :: t} {b} with map f (t ++ b) | map-++-comm {A} {B} {f} {t} {b}
  map-++-comm {A} {B} {f} {h :: t} {b} | _ | refl = refl

  -- foldl theorem
  foldl-++ : {A B : Set} {l1 l2 : List A} {f : B → A → B} {b0 : B} →
              foldl f b0 (l1 ++ l2) == foldl f (foldl f b0 l1) l2
  foldl-++ {l1 = []} = refl
  foldl-++ {l1 = a1 :: l1rest} = foldl-++ {l1 = l1rest}

  {- TODO either delete these, or add metatheorems for them
  zip : {A B : Set} → (a : List A) → (b : List B) → ∥ a ∥ == ∥ b ∥ → List (A × B)
  zip [] [] eqH = []
  zip [] (b :: bs) ()
  zip (a :: as) [] ()
  zip (a :: as) (b :: bs) eqH = (a , b) :: zip as bs (1+EQ eqH)
  -}

  -- TODO what things below do we actually need?

  data _in-List_ {A : Set} : A → List A → Set where
    InH : {a : A} {as : List A} → a in-List (a :: as)
    InT : {a a' : A} {as : List A} → a in-List as → a in-List (a' :: as)

  ∅∈l→l==[] : {A : Set} {l : List A} → ((a : A) → a in-List l → ⊥) → l == []
  ∅∈l→l==[] {l = []} h = refl
  ∅∈l→l==[] {l = a' :: as} h = abort (h a' InH)

  a∉a'::as→a∉as : {A : Set} →
                    {as : List A} →
                    {a a' : A} →
                    (==dec : (a₁ a₂ : A) → (a₁ == a₂) ∨ ((a₁ == a₂) → ⊥)) →
                    (a in-List (a' :: as) → ⊥) →
                    a in-List as →
                    ⊥
  a∉a'::as→a∉as _ h h' = h (InT h')

  not-in-append-comm : {A : Set} {x : A} {l₁ l₂ : List A} → ((a₁ a₂ : A) → (a₁ == a₂) ∨ ((a₁ == a₂) → ⊥)) → (x in-List l₁ → ⊥) → (x in-List l₂ → ⊥) → x in-List (l₁ ++ l₂) → ⊥
  not-in-append-comm {x = x} {[]} {l₂} ==dec h₁ h₂ h₃ = h₂ h₃
  not-in-append-comm {x = x} {a₁ :: as₁} {l₂} ==dec h₁ h₂ h₃   with  ==dec a₁ x
  not-in-append-comm {x = x} {a₁ :: as₁} {l₂} ==dec h₁ h₂ h₃       | Inl h      = h₁ (tr (λ y → y in-List (a₁ :: as₁)) h InH)
  not-in-append-comm {x = .a₁} {a₁ :: as₁} {l₂} ==dec h₁ h₂ InH    | Inr h      = abort (h refl)
  not-in-append-comm {x = x} {a₁ :: as₁} {l₂} ==dec h₁ h₂ (InT h₃) | Inr h      = not-in-append-comm ==dec (a∉a'::as→a∉as ==dec h₁) h₂ h₃

  remove-all : {A : Set} → ((a₁ a₂ : A) → (a₁ == a₂) ∨ ((a₁ == a₂) → ⊥)) → List A → A → List A
  remove-all ==dec [] a = []
  remove-all ==dec (a' :: as) a
    with ==dec a a' | remove-all ==dec as a
  ...  | Inl _      | l'                    = l'
  ...  | Inr _      | l'                    = a' :: l'

  remove-all-append-comm : {A : Set} →
                           (==dec : (a₁ a₂ : A) → (a₁ == a₂) ∨ ((a₁ == a₂) → ⊥)) →
                           (l₁ l₂ : List A) →
                           (a : A) →
                           remove-all ==dec l₁ a ++ remove-all ==dec l₂ a == remove-all ==dec (l₁ ++ l₂) a
  remove-all-append-comm ==dec [] l₂ a = refl
  remove-all-append-comm ==dec (a₁ :: as₁) l₂ a with ==dec a a₁ | remove-all-append-comm ==dec as₁ l₂ a
  remove-all-append-comm ==dec (a₁ :: as₁) l₂ a    | Inl refl   | h                                      = h
  remove-all-append-comm ==dec (a₁ :: as₁) l₂ a    | Inr _      | h                                      = ap1 (λ y → a₁ :: y) h

  remove-all-not-in : {A : Set} →
                      (==dec : (a₁ a₂ : A) → (a₁ == a₂) ∨ ((a₁ == a₂) → ⊥)) →
                      (l : List A) →
                      (a : A) →
                      a in-List remove-all ==dec l a →
                      ⊥
  remove-all-not-in ==dec [] a ()
  remove-all-not-in ==dec (a' :: as) a h with    ==dec a a'
  remove-all-not-in ==dec (a' :: as) a h       | Inl refl   = remove-all-not-in ==dec as a' h
  remove-all-not-in ==dec (a' :: as) .a' InH   | Inr a≠a'   = a≠a' refl
  remove-all-not-in ==dec (a' :: as) a (InT h) | Inr a≠a'   = remove-all-not-in ==dec as a h

  a∉l→a∉remove-all-l-a' : {A : Set} →
                            {l : List A} →
                            {a a' : A} →
                            (==dec : (a₁ a₂ : A) → (a₁ == a₂) ∨ ((a₁ == a₂) → ⊥)) →
                            (a in-List l → ⊥) →
                            a in-List remove-all ==dec l a' →
                            ⊥
  a∉l→a∉remove-all-l-a' {l = []} {a} _ h₁ h₂ = h₁ h₂
  a∉l→a∉remove-all-l-a' {l = lh :: lt} {a} {a'} ==dec h₁ h₂   with  ==dec a lh | ==dec a' lh
  a∉l→a∉remove-all-l-a' {l = lh :: lt} {a} {a'} ==dec h₁ h₂       | Inl a==lh  | _            = h₁ (tr (λ y → a in-List (y :: lt) ) a==lh InH)
  a∉l→a∉remove-all-l-a' {_} {lh :: lt} {a} {a'} ==dec h₁ h₂       | Inr _      | Inl _        = a∉l→a∉remove-all-l-a' ==dec (a∉a'::as→a∉as ==dec h₁) h₂
  a∉l→a∉remove-all-l-a' {_} {lh :: lt} {.lh} {a'} ==dec h₁ InH    | Inr a≠lh   | Inr _        = a≠lh refl
  a∉l→a∉remove-all-l-a' {_} {lh :: lt} {a} {a'} ==dec h₁ (InT h₂) | Inr _      | Inr _        = a∉l→a∉remove-all-l-a' ==dec (a∉a'::as→a∉as ==dec h₁) h₂
