open import Prelude
open import Nat
open import Agda.Primitive using (Level; lzero; lsuc) renaming (_⊔_ to lmax)

module List where

  data List {l : Level} (A : Set l) : Set l where
    [] : List A
    _::_ : A → List A → List A

  _++_ : {l : Level} {A : Set l} → List A → List A → List A
  [] ++ l₂ = l₂
  (h :: l₁) ++ l₂ = h :: (l₁ ++ l₂)

  infixl 50 _++_

  ++assc : ∀{l A a1 a2 a3} → (_++_ {l} {A} a1 a2) ++ a3 == a1 ++ (a2 ++ a3)
  ++assc {l} {A} {[]} {a2} {a3} = refl
  ++assc {l} {A} {x :: a1} {a2} {a3} with a1 ++ a2 ++ a3 | ++assc {l} {A} {a1} {a2} {a3}
  ++assc {l} {A} {x :: a1} {a2} {a3} | _ | refl = refl

  map : {lA lB : Level} → {A : Set lA} → {B : Set lB} → (A → B) → List A → List B
  map f [] = []
  map f (a :: as) = f a :: map f as

  map-++-comm : ∀{l1 l2 A B f a b} → map f a ++ map f b == map {l1} {l2} {A} {B} f (a ++ b)
  map-++-comm {a = []} = refl
  map-++-comm {l1} {l2} {A} {B} {f} {h :: t} {b} with map f (t ++ b) | map-++-comm {l1} {l2} {A} {B} {f} {t} {b}
  map-++-comm {l1} {l2} {A} {B} {f} {h :: t} {b} | _ | refl = refl

  ∥_∥ : {l : Level} {A : Set l} → List A → Nat
  ∥ [] ∥ = Z
  ∥ a :: as ∥ = 1+ ∥ as ∥

  ∥-++-comm : ∀{l A a1 a2} → ∥ a1 ∥ + (∥_∥ {l} {A} a2) == ∥ a1 ++ a2 ∥
  ∥-++-comm {l} {A} {[]} {a2} = refl
  ∥-++-comm {l} {A} {a :: a1} {a2} = 1+ap (∥-++-comm {l} {A} {a1})

  _⟦_given_⟧ : {l : Level} {A : Set l} → (la : List A) → (i : Nat) → i < ∥ la ∥ → A
  [] ⟦ i given h ⟧ = abort (n≮0 h)
  (a :: as) ⟦ Z given h ⟧ = a
  (a :: as) ⟦ 1+ i given h ⟧ = as ⟦ i given 1+n<1+m→n<m h ⟧

  ⦇l1++[a]++l2⦈⟦∥l1∥⟧==a : {l : Level} {A : Set l} {l1 l2 : List A} {a : A} →
                             (h : ∥ l1 ∥ < ∥ l1 ++ (a :: []) ++ l2 ∥) →
                             ((l1 ++ (a :: []) ++ l2) ⟦ ∥ l1 ∥ given h ⟧ == a)
  ⦇l1++[a]++l2⦈⟦∥l1∥⟧==a {l1 = []} h = refl
  ⦇l1++[a]++l2⦈⟦∥l1∥⟧==a {l1 = a1 :: l1rest} {l2} {a} h = ⦇l1++[a]++l2⦈⟦∥l1∥⟧==a {l1 = l1rest} {l2} {a} (1+n<1+m→n<m h)

  foldl : {ℓ1 ℓ2 : Level} → {A : Set ℓ1} → {B : Set ℓ2} → (B → A → B) → B → List A → B
  foldl f b [] = b
  foldl f b (a :: as) = foldl f (f b a) as

  foldl-++ : {ℓ1 ℓ2 : Level} {A : Set ℓ1} {B : Set ℓ2} {l1 l2 : List A} {f : B → A → B} {b0 : B} →
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
