open import Nat
open import Prelude
open import List

open import contexts
open import core

-- This file is a glorious testament to all of agda's greatest strengths -
-- a beautiful work that will shine brightly throughout the ages and instill
-- hope for the future in many generations to come. May I never use any other
-- proof assistant.
module decidability where
  mutual
    -- We define context and list decidability in their respective files,
    -- because they're important metatheorems. However, each accepts a
    -- decidability theorem for its value type, and for environments that
    -- value type is result, so the termination checker complains. To fix
    -- this, we redefine type-specific versions of these theorems here.

    list<result>-==-dec : (l1 l2 : List result) →
                           l1 == l2 ∨ l1 ≠ l2
    list<result>-==-dec [] []       = Inl refl
    list<result>-==-dec [] (_ :: _) = Inr (λ ())
    list<result>-==-dec (_ :: _) [] = Inr (λ ())
    list<result>-==-dec (h1 :: t1) (h2 :: t2)
      with result-==-dec h1 h2
    ... | Inr ne = Inr (λ where refl → ne refl)
    ... | Inl refl
      with list<result>-==-dec t1 t2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl

    list<exp>-==-dec : (l1 l2 : List exp) →
                        l1 == l2 ∨ l1 ≠ l2
    list<exp>-==-dec [] []       = Inl refl
    list<exp>-==-dec [] (_ :: _) = Inr (λ ())
    list<exp>-==-dec (_ :: _) [] = Inr (λ ())
    list<exp>-==-dec (h1 :: t1) (h2 :: t2)
      with exp-==-dec h1 h2
    ... | Inr ne = Inr (λ where refl → ne refl)
    ... | Inl refl
      with list<exp>-==-dec t1 t2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl

    list<rule>-==-dec : (l1 l2 : List rule) →
                         l1 == l2 ∨ l1 ≠ l2
    list<rule>-==-dec [] []       = Inl refl
    list<rule>-==-dec [] (_ :: _) = Inr (λ ())
    list<rule>-==-dec (_ :: _) [] = Inr (λ ())
    list<rule>-==-dec ((|C[ c1 ] x1 => e1) :: t1) ((|C[ c2 ] x2 => e2) :: t2)
      with natEQ c1 c2
    ... | Inr ne = Inr (λ where refl → ne refl)
    ... | Inl refl
      with natEQ x1 x2
    ... | Inr ne = Inr (λ where refl → ne refl)
    ... | Inl refl
      with exp-==-dec e1 e2
    ... | Inr ne = Inr (λ where refl → ne refl)
    ... | Inl refl
      with list<rule>-==-dec t1 t2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl

    list<ex>-==-dec : (l1 l2 : List ex) →
                         l1 == l2 ∨ l1 ≠ l2
    list<ex>-==-dec [] []       = Inl refl
    list<ex>-==-dec [] (_ :: _) = Inr (λ ())
    list<ex>-==-dec (_ :: _) [] = Inr (λ ())
    list<ex>-==-dec (ex1 :: t1) (ex2 :: t2)
      with ex-==-dec ex1 ex2
    ... | Inr ne = Inr (λ where refl → ne refl)
    ... | Inl refl
      with list<ex>-==-dec t1 t2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl

    ctx<result>-==-dec : (Γ1 Γ2 : result ctx) →
                          Γ1 == Γ2 ∨ Γ1 ≠ Γ2
    ctx<result>-==-dec [] []       = Inl refl
    ctx<result>-==-dec [] (_ :: _) = Inr (λ ())
    ctx<result>-==-dec (_ :: _) [] = Inr (λ ())
    ctx<result>-==-dec ((hx1 , hr1) :: t1) ((hx2 , hr2) :: t2)
      with natEQ hx1 hx2 | result-==-dec hr1 hr2 | ctx<result>-==-dec t1 t2
    ... | Inl refl | Inl refl | Inl refl = Inl refl
    ... | Inl refl | Inl refl | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl | Inr ne   | _        = Inr λ where refl → ne refl
    ... | Inr ne   | _        | _        = Inr λ where refl → ne refl

    pf-==-dec : (pf1 pf2 : pf) →
                 pf1 == pf2 ∨ pf1 ≠ pf2
    pf-==-dec [] []       = Inl refl
    pf-==-dec [] (_ :: _) = Inr (λ ())
    pf-==-dec (_ :: _) [] = Inr (λ ())
    pf-==-dec ((r1 , ex1) :: t1) ((r2 , ex2) :: t2)
      with result-==-dec r1 r2
    ... | Inr ne = Inr (λ where refl → ne refl)
    ... | Inl refl
      with ex-==-dec ex1 ex2
    ... | Inr ne = Inr (λ where refl → ne refl)
    ... | Inl refl
      with pf-==-dec t1 t2
    ... | Inr ne = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl

    ex-==-dec : (ex1 ex2 : ex) →
                 ex1 == ex2 ∨ ex1 ≠ ex2
    ex-==-dec (PF pf1) (PF pf2)
      with pf-==-dec pf1 pf2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    ex-==-dec (PF _) ⟨ _ ⟩ = Inr (λ ())
    ex-==-dec (PF _) (C[ _ ] ex2) = Inr (λ ())
    ex-==-dec ⟨ exs1 ⟩ ⟨ exs2 ⟩
      with list<ex>-==-dec exs1 exs2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    ex-==-dec ⟨ _ ⟩ (PF _) = Inr (λ ())
    ex-==-dec ⟨ _ ⟩ (C[ _ ] _) = Inr (λ ())
    ex-==-dec (C[ c1 ] ex1) (C[ c2 ] ex2)
      with natEQ c1 c2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl
      with ex-==-dec ex1 ex2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    ex-==-dec (C[ _ ] _) (PF _) = Inr (λ ())
    ex-==-dec (C[ _ ] _) ⟨ _ ⟩ = Inr (λ ())

    exp-==-dec : (e1 e2 : exp) → e1 == e2 ∨ e1 ≠ e2
    exp-==-dec (·λ x1 => e1) (·λ x2 => e2)
      with natEQ x1 x2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl
      with exp-==-dec e1 e2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    exp-==-dec (·λ x1 => e1) fix x ⦇·λ x₁ => e2 ·⦈ = Inr (λ ())
    exp-==-dec (·λ x1 => e1) X[ x ] = Inr (λ ())
    exp-==-dec (·λ x1 => e1) (e2 ∘ e3) = Inr (λ ())
    exp-==-dec (·λ x1 => e1) ⟨ x ⟩ = Inr (λ ())
    exp-==-dec (·λ x1 => e1) (get[ x th-of x₁ ] e2) = Inr (λ ())
    exp-==-dec (·λ x1 => e1) (C[ x ] e2) = Inr (λ ())
    exp-==-dec (·λ x1 => e1) case e2 of⦃· x ·⦄ = Inr (λ ())
    exp-==-dec (·λ x1 => e1) ??[ x ] = Inr (λ ())
    exp-==-dec (·λ x1 => e1) (PF x) = Inr (λ ())
    exp-==-dec (·λ x1 => e1) (PBE:assert e2 e3) = Inr (λ ())
    exp-==-dec fix f1 ⦇·λ x1 => e1 ·⦈ fix f2 ⦇·λ x2 => e2 ·⦈
      with natEQ f1 f2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl
      with natEQ x1 x2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl
      with exp-==-dec e1 e2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    exp-==-dec fix f1 ⦇·λ x1 => e1 ·⦈ (·λ x => e2) = Inr (λ ())
    exp-==-dec fix f1 ⦇·λ x1 => e1 ·⦈ X[ x ] = Inr (λ ())
    exp-==-dec fix f1 ⦇·λ x1 => e1 ·⦈ (e2 ∘ e3) = Inr (λ ())
    exp-==-dec fix f1 ⦇·λ x1 => e1 ·⦈ ⟨ x ⟩ = Inr (λ ())
    exp-==-dec fix f1 ⦇·λ x1 => e1 ·⦈ (get[ x th-of x₁ ] e2) = Inr (λ ())
    exp-==-dec fix f1 ⦇·λ x1 => e1 ·⦈ (C[ x ] e2) = Inr (λ ())
    exp-==-dec fix f1 ⦇·λ x1 => e1 ·⦈ case e2 of⦃· x ·⦄ = Inr (λ ())
    exp-==-dec fix f1 ⦇·λ x1 => e1 ·⦈ ??[ x ] = Inr (λ ())
    exp-==-dec fix f1 ⦇·λ x1 => e1 ·⦈ (PF x) = Inr (λ ())
    exp-==-dec fix f1 ⦇·λ x1 => e1 ·⦈ (PBE:assert e2 e3) = Inr (λ ())
    exp-==-dec X[ x1 ] X[ x2 ]
      with natEQ x1 x2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    exp-==-dec X[ x1 ] (·λ x => e2) = Inr (λ ())
    exp-==-dec X[ x1 ] fix x ⦇·λ x₁ => e2 ·⦈ = Inr (λ ())
    exp-==-dec X[ x1 ] (e2 ∘ e3) = Inr (λ ())
    exp-==-dec X[ x1 ] ⟨ x ⟩ = Inr (λ ())
    exp-==-dec X[ x1 ] (get[ x th-of x₁ ] e2) = Inr (λ ())
    exp-==-dec X[ x1 ] (C[ x ] e2) = Inr (λ ())
    exp-==-dec X[ x1 ] case e2 of⦃· x ·⦄ = Inr (λ ())
    exp-==-dec X[ x1 ] ??[ x ] = Inr (λ ())
    exp-==-dec X[ x1 ] (PF x) = Inr (λ ())
    exp-==-dec X[ x1 ] (PBE:assert e2 e3) = Inr (λ ())
    exp-==-dec (ef1 ∘ earg1) (ef2 ∘ earg2)
      with exp-==-dec ef1 ef2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl
      with exp-==-dec earg1 earg2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    exp-==-dec (ef1 ∘ earg1) (·λ x => e2) = Inr (λ ())
    exp-==-dec (ef1 ∘ earg1) fix x ⦇·λ x₁ => e2 ·⦈ = Inr (λ ())
    exp-==-dec (ef1 ∘ earg1) X[ x ] = Inr (λ ())
    exp-==-dec (ef1 ∘ earg1) ⟨ x ⟩ = Inr (λ ())
    exp-==-dec (ef1 ∘ earg1) (get[ x th-of x₁ ] e2) = Inr (λ ())
    exp-==-dec (ef1 ∘ earg1) (C[ x ] e2) = Inr (λ ())
    exp-==-dec (ef1 ∘ earg1) case e2 of⦃· x ·⦄ = Inr (λ ())
    exp-==-dec (ef1 ∘ earg1) ??[ x ] = Inr (λ ())
    exp-==-dec (ef1 ∘ earg1) (PF x) = Inr (λ ())
    exp-==-dec (ef1 ∘ earg1) (PBE:assert e2 e3) = Inr (λ ())
    exp-==-dec ⟨ es1 ⟩ ⟨ es2 ⟩
      with list<exp>-==-dec es1 es2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    exp-==-dec ⟨ es1 ⟩ (·λ x => e2) = Inr (λ ())
    exp-==-dec ⟨ es1 ⟩ fix x ⦇·λ x₁ => e2 ·⦈ = Inr (λ ())
    exp-==-dec ⟨ es1 ⟩ X[ x ] = Inr (λ ())
    exp-==-dec ⟨ es1 ⟩ (e2 ∘ e3) = Inr (λ ())
    exp-==-dec ⟨ es1 ⟩ (get[ x th-of x₁ ] e2) = Inr (λ ())
    exp-==-dec ⟨ es1 ⟩ (C[ x ] e2) = Inr (λ ())
    exp-==-dec ⟨ es1 ⟩ case e2 of⦃· x ·⦄ = Inr (λ ())
    exp-==-dec ⟨ es1 ⟩ ??[ x ] = Inr (λ ())
    exp-==-dec ⟨ es1 ⟩ (PF x) = Inr (λ ())
    exp-==-dec ⟨ es1 ⟩ (PBE:assert e2 e3) = Inr (λ ())
    exp-==-dec (get[ i1 th-of n1 ] e1) (get[ i2 th-of n2 ] e2)
      with natEQ i1 i2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl
      with natEQ n1 n2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl
      with exp-==-dec e1 e2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    exp-==-dec (get[ i1 th-of n1 ] e1) (·λ x => e2) = Inr (λ ())
    exp-==-dec (get[ i1 th-of n1 ] e1) fix x ⦇·λ x₁ => e2 ·⦈ = Inr (λ ())
    exp-==-dec (get[ i1 th-of n1 ] e1) X[ x ] = Inr (λ ())
    exp-==-dec (get[ i1 th-of n1 ] e1) (e2 ∘ e3) = Inr (λ ())
    exp-==-dec (get[ i1 th-of n1 ] e1) ⟨ x ⟩ = Inr (λ ())
    exp-==-dec (get[ i1 th-of n1 ] e1) (C[ x ] e2) = Inr (λ ())
    exp-==-dec (get[ i1 th-of n1 ] e1) case e2 of⦃· x ·⦄ = Inr (λ ())
    exp-==-dec (get[ i1 th-of n1 ] e1) ??[ x ] = Inr (λ ())
    exp-==-dec (get[ i1 th-of n1 ] e1) (PF x) = Inr (λ ())
    exp-==-dec (get[ i1 th-of n1 ] e1) (PBE:assert e2 e3) = Inr (λ ())
    exp-==-dec (C[ c1 ] e1) (C[ c2 ] e2)
      with natEQ c1 c2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl
      with exp-==-dec e1 e2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    exp-==-dec (C[ c1 ] e1) (·λ x => e2) = Inr (λ ())
    exp-==-dec (C[ c1 ] e1) fix x ⦇·λ x₁ => e2 ·⦈ = Inr (λ ())
    exp-==-dec (C[ c1 ] e1) X[ x ] = Inr (λ ())
    exp-==-dec (C[ c1 ] e1) (e2 ∘ e3) = Inr (λ ())
    exp-==-dec (C[ c1 ] e1) ⟨ x ⟩ = Inr (λ ())
    exp-==-dec (C[ c1 ] e1) (get[ x th-of x₁ ] e2) = Inr (λ ())
    exp-==-dec (C[ c1 ] e1) case e2 of⦃· x ·⦄ = Inr (λ ())
    exp-==-dec (C[ c1 ] e1) ??[ x ] = Inr (λ ())
    exp-==-dec (C[ c1 ] e1) (PF x) = Inr (λ ())
    exp-==-dec (C[ c1 ] e1) (PBE:assert e2 e3) = Inr (λ ())
    exp-==-dec case e1 of⦃· rules1 ·⦄ case e2 of⦃· rules2 ·⦄
      with exp-==-dec e1 e2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl
      with list<rule>-==-dec rules1 rules2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    exp-==-dec case e1 of⦃· rules1 ·⦄ (·λ x => e2) = Inr (λ ())
    exp-==-dec case e1 of⦃· rules1 ·⦄ fix x ⦇·λ x₁ => e2 ·⦈ = Inr (λ ())
    exp-==-dec case e1 of⦃· rules1 ·⦄ X[ x ] = Inr (λ ())
    exp-==-dec case e1 of⦃· rules1 ·⦄ (e2 ∘ e3) = Inr (λ ())
    exp-==-dec case e1 of⦃· rules1 ·⦄ ⟨ x ⟩ = Inr (λ ())
    exp-==-dec case e1 of⦃· rules1 ·⦄ (get[ x th-of x₁ ] e2) = Inr (λ ())
    exp-==-dec case e1 of⦃· rules1 ·⦄ (C[ x ] e2) = Inr (λ ())
    exp-==-dec case e1 of⦃· rules1 ·⦄ ??[ x ] = Inr (λ ())
    exp-==-dec case e1 of⦃· rules1 ·⦄ (PF x) = Inr (λ ())
    exp-==-dec case e1 of⦃· rules1 ·⦄ (PBE:assert e2 e3) = Inr (λ ())
    exp-==-dec ??[ u1 ] ??[ u2 ]
      with natEQ u1 u2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    exp-==-dec ??[ u1 ] (·λ x => e2) = Inr (λ ())
    exp-==-dec ??[ u1 ] fix x ⦇·λ x₁ => e2 ·⦈ = Inr (λ ())
    exp-==-dec ??[ u1 ] X[ x ] = Inr (λ ())
    exp-==-dec ??[ u1 ] (e2 ∘ e3) = Inr (λ ())
    exp-==-dec ??[ u1 ] ⟨ x ⟩ = Inr (λ ())
    exp-==-dec ??[ u1 ] (get[ x th-of x₁ ] e2) = Inr (λ ())
    exp-==-dec ??[ u1 ] (C[ x ] e2) = Inr (λ ())
    exp-==-dec ??[ u1 ] case e2 of⦃· x ·⦄ = Inr (λ ())
    exp-==-dec ??[ u1 ] (PF x) = Inr (λ ())
    exp-==-dec ??[ u1 ] (PBE:assert e2 e3) = Inr (λ ())
    exp-==-dec (PF pf1) (PF pf2)
      with pf-==-dec pf1 pf2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    exp-==-dec (PF pf1) (·λ x => e2) = Inr (λ ())
    exp-==-dec (PF pf1) fix x ⦇·λ x₁ => e2 ·⦈ = Inr (λ ())
    exp-==-dec (PF pf1) X[ x ] = Inr (λ ())
    exp-==-dec (PF pf1) (e2 ∘ e3) = Inr (λ ())
    exp-==-dec (PF pf1) ⟨ x ⟩ = Inr (λ ())
    exp-==-dec (PF pf1) (get[ x th-of x₁ ] e2) = Inr (λ ())
    exp-==-dec (PF pf1) (C[ x ] e2) = Inr (λ ())
    exp-==-dec (PF pf1) case e2 of⦃· x ·⦄ = Inr (λ ())
    exp-==-dec (PF pf1) ??[ x ] = Inr (λ ())
    exp-==-dec (PF pf1) (PBE:assert e2 e3) = Inr (λ ())
    exp-==-dec (PBE:assert e1a e1b) (PBE:assert e2a e2b)
      with exp-==-dec e1a e2a
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl
      with exp-==-dec e1b e2b
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    exp-==-dec (PBE:assert e1a e1b) (·λ x => e2) = Inr (λ ())
    exp-==-dec (PBE:assert e1a e1b) fix x ⦇·λ x₁ => e2 ·⦈ = Inr (λ ())
    exp-==-dec (PBE:assert e1a e1b) X[ x ] = Inr (λ ())
    exp-==-dec (PBE:assert e1a e1b) (e2 ∘ e3) = Inr (λ ())
    exp-==-dec (PBE:assert e1a e1b) ⟨ x ⟩ = Inr (λ ())
    exp-==-dec (PBE:assert e1a e1b) (get[ x th-of x₁ ] e2) = Inr (λ ())
    exp-==-dec (PBE:assert e1a e1b) (C[ x ] e2) = Inr (λ ())
    exp-==-dec (PBE:assert e1a e1b) case e2 of⦃· x ·⦄ = Inr (λ ())
    exp-==-dec (PBE:assert e1a e1b) ??[ x ] = Inr (λ ())
    exp-==-dec (PBE:assert e1a e1b) (PF x) = Inr (λ ())

    result-==-dec : (r1 r2 : result) → r1 == r2 ∨ r1 ≠ r2
    result-==-dec ([ E1 ]λ x1 => e1) ([ E2 ]λ x2 => e2)
      with ctx<result>-==-dec E1 E2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl
      with natEQ x1 x2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl
      with exp-==-dec e1 e2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl = Inl refl
    result-==-dec ([ E ]λ x => e) [ _ ]fix _ ⦇·λ _ => _ ·⦈ = Inr λ ()
    result-==-dec ([ E ]λ x => e) ⟨ _ ⟩ = Inr (λ ())
    result-==-dec ([ E ]λ x => e) (C[ _ ] _) = Inr (λ ())
    result-==-dec ([ E ]λ x => e) [ _ ]??[ _ ] = Inr (λ ())
    result-==-dec ([ E ]λ x => e) (_ ∘ _) = Inr (λ ())
    result-==-dec ([ E ]λ x => e) (get[ _ th-of _ ] _) = Inr (λ ())
    result-==-dec ([ E ]λ x => e) [ _ ]case _ of⦃· _ ·⦄ = Inr (λ ())
    result-==-dec ([ E ]λ x => e) (PF _) = Inr (λ ())
    result-==-dec [ E1 ]fix f1 ⦇·λ x1 => e1 ·⦈ [ E2 ]fix f2 ⦇·λ x2 => e2 ·⦈
      with ctx<result>-==-dec E1 E2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl
      with natEQ f1 f2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl
      with natEQ x1 x2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl
      with exp-==-dec e1 e2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl = Inl refl
    result-==-dec [ E ]fix f ⦇·λ x => e ·⦈ ([ _ ]λ _ => _) = Inr (λ ())
    result-==-dec [ E ]fix f ⦇·λ x => e ·⦈ ⟨ _ ⟩ = Inr (λ ())
    result-==-dec [ E ]fix f ⦇·λ x => e ·⦈ (C[ _ ] _) = Inr (λ ())
    result-==-dec [ E ]fix f ⦇·λ x => e ·⦈ [ _ ]??[ _ ] = Inr (λ ())
    result-==-dec [ E ]fix f ⦇·λ x => e ·⦈ (_ ∘ _) = Inr (λ ())
    result-==-dec [ E ]fix f ⦇·λ x => e ·⦈ (get[ _ th-of _ ] _) = Inr (λ ())
    result-==-dec [ E ]fix f ⦇·λ x => e ·⦈ [ _ ]case _ of⦃· _ ·⦄ = Inr (λ ())
    result-==-dec [ E ]fix f ⦇·λ x => e ·⦈ (PF _) = Inr (λ ())
    result-==-dec ⟨ rs1 ⟩ ⟨ rs2 ⟩
      with list<result>-==-dec rs1 rs2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl = Inl refl
    result-==-dec ⟨ rs1 ⟩ ([ _ ]λ _ => _) = Inr (λ ())
    result-==-dec ⟨ rs1 ⟩ [ _ ]fix _ ⦇·λ _ => _ ·⦈ = Inr (λ ())
    result-==-dec ⟨ rs1 ⟩ (C[ _ ] _) = Inr (λ ())
    result-==-dec ⟨ rs1 ⟩ [ _ ]??[ _ ] = Inr (λ ())
    result-==-dec ⟨ rs1 ⟩ (_ ∘ _) = Inr (λ ())
    result-==-dec ⟨ rs1 ⟩ (get[ _ th-of _ ] _) = Inr (λ ())
    result-==-dec ⟨ rs1 ⟩ [ _ ]case _ of⦃· _ ·⦄ = Inr (λ ())
    result-==-dec ⟨ rs1 ⟩ (PF _) = Inr (λ ())
    result-==-dec (C[ c1 ] r1) (C[ c2 ] r2)
      with natEQ c1 c2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl
      with result-==-dec r1 r2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl = Inl refl
    result-==-dec (C[ c ] r) ([ _ ]λ _ => _) = Inr (λ ())
    result-==-dec (C[ c ] r) [ _ ]fix _ ⦇·λ _ => _ ·⦈ = Inr (λ ())
    result-==-dec (C[ c ] r) ⟨ _ ⟩ = Inr (λ ())
    result-==-dec (C[ c ] r) [ _ ]??[ _ ] = Inr (λ ())
    result-==-dec (C[ c ] r) (_ ∘ _) = Inr (λ ())
    result-==-dec (C[ c ] r) (get[ _ th-of _ ] _) = Inr (λ ())
    result-==-dec (C[ c ] r) [ _ ]case _ of⦃· _ ·⦄ = Inr (λ ())
    result-==-dec (C[ c ] r) (PF _) = Inr (λ ())
    result-==-dec [ E1 ]??[ u1 ] [ E2 ]??[ u2 ]
      with ctx<result>-==-dec E1 E2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl
      with natEQ u1 u2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl = Inl refl
    result-==-dec [ E ]??[ u1 ] ([ _ ]λ _ => _) = Inr (λ ())
    result-==-dec [ E ]??[ u1 ] [ _ ]fix _ ⦇·λ _ => _ ·⦈ = Inr (λ ())
    result-==-dec [ E ]??[ u1 ] ⟨ _ ⟩ = Inr (λ ())
    result-==-dec [ E ]??[ u1 ] (C[ _ ] _) = Inr (λ ())
    result-==-dec [ E ]??[ u1 ] (_ ∘ _) = Inr (λ ())
    result-==-dec [ E ]??[ u1 ] (get[ _ th-of _ ] _) = Inr (λ ())
    result-==-dec [ E ]??[ u1 ] [ _ ]case _ of⦃· _ ·⦄ = Inr (λ ())
    result-==-dec [ E ]??[ u1 ] (PF _) = Inr (λ ())
    result-==-dec (rf1 ∘ rarg1) (rf2 ∘ rarg2)
      with result-==-dec rf1 rf2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl
      with result-==-dec rarg1 rarg2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl = Inl refl
    result-==-dec (rf ∘ rarg) ([ _ ]λ _ => _) = Inr (λ ())
    result-==-dec (rf ∘ rarg) [ _ ]fix _ ⦇·λ _ => _ ·⦈ = Inr (λ ())
    result-==-dec (rf ∘ rarg) ⟨ _ ⟩ = Inr (λ ())
    result-==-dec (rf ∘ rarg) (C[ _ ] _) = Inr (λ ())
    result-==-dec (rf ∘ rarg) [ _ ]??[ _ ] = Inr (λ ())
    result-==-dec (rf ∘ rarg) (get[ _ th-of _ ] _) = Inr (λ ())
    result-==-dec (rf ∘ rarg) [ _ ]case _ of⦃· _ ·⦄ = Inr (λ ())
    result-==-dec (rf ∘ rarg) (PF _) = Inr (λ ())
    result-==-dec (get[ i1 th-of n1 ] r1) (get[ i2 th-of n2 ] r2)
      with natEQ i1 i2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl
      with natEQ n1 n2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl
      with result-==-dec r1 r2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl = Inl refl
    result-==-dec (get[ i th-of n ] r) ([ _ ]λ _ => _) = Inr (λ ())
    result-==-dec (get[ i th-of n ] r) [ _ ]fix _ ⦇·λ _ => _ ·⦈ = Inr (λ ())
    result-==-dec (get[ i th-of n ] r) ⟨ _ ⟩ = Inr (λ ())
    result-==-dec (get[ i th-of n ] r) (C[ _ ] _) = Inr (λ ())
    result-==-dec (get[ i th-of n ] r) [ _ ]??[ _ ] = Inr (λ ())
    result-==-dec (get[ i th-of n ] r) (_ ∘ _) = Inr (λ ())
    result-==-dec (get[ i th-of n ] r) [ _ ]case _ of⦃· _ ·⦄ = Inr (λ ())
    result-==-dec (get[ i th-of n ] r) (PF _) = Inr (λ ())
    result-==-dec [ E1 ]case r1 of⦃· rules1 ·⦄ [ E2 ]case r2 of⦃· rules2 ·⦄
      with ctx<result>-==-dec E1 E2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl
      with result-==-dec r1 r2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl
      with list<rule>-==-dec rules1 rules2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl = Inl refl
    result-==-dec [ E ]case r of⦃· rules ·⦄ ([ _ ]λ _ => _) = Inr (λ ())
    result-==-dec [ E ]case r of⦃· rules ·⦄ [ _ ]fix _ ⦇·λ _ => _ ·⦈ = Inr (λ ())
    result-==-dec [ E ]case r of⦃· rules ·⦄ ⟨ _ ⟩ = Inr (λ ())
    result-==-dec [ E ]case r of⦃· rules ·⦄ (C[ _ ] _) = Inr (λ ())
    result-==-dec [ E ]case r of⦃· rules ·⦄ [ _ ]??[ _ ] = Inr (λ ())
    result-==-dec [ E ]case r of⦃· rules ·⦄ (_ ∘ _) = Inr (λ ())
    result-==-dec [ E ]case r of⦃· rules ·⦄ (get[ _ th-of _ ] _) = Inr (λ ())
    result-==-dec [ E ]case r of⦃· rules ·⦄ (PF _) = Inr (λ ())
    result-==-dec (PF pf1) (PF pf2)
      with pf-==-dec pf1 pf2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl = Inl refl
    result-==-dec (PF pf) ([ _ ]λ _ => _) = Inr (λ ())
    result-==-dec (PF pf) [ _ ]fix _ ⦇·λ _ => _ ·⦈ = Inr (λ ())
    result-==-dec (PF pf) ⟨ _ ⟩ = Inr (λ ())
    result-==-dec (PF pf) (C[ _ ] _) = Inr (λ ())
    result-==-dec (PF pf) [ _ ]??[ _ ] = Inr (λ ())
    result-==-dec (PF pf) (_ ∘ _) = Inr (λ ())
    result-==-dec (PF pf) (get[ _ th-of _ ] _) = Inr (λ ())
    result-==-dec (PF pf) [ _ ]case _ of⦃· _ ·⦄ = Inr (λ ())

  mutual
    list<typ>-==-dec : (l1 l2 : List typ) →
                        l1 == l2 ∨ l1 ≠ l2
    list<typ>-==-dec [] []       = Inl refl
    list<typ>-==-dec [] (_ :: _) = Inr (λ ())
    list<typ>-==-dec (_ :: _) [] = Inr (λ ())
    list<typ>-==-dec (τ1 :: t1) (τ2 :: t2)
      with typ-==-dec τ1 τ2
    ... | Inr ne = Inr (λ where refl → ne refl)
    ... | Inl refl
      with list<typ>-==-dec t1 t2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl

    typ-==-dec : (τ1 τ2 : typ) → τ1 == τ2 ∨ τ1 ≠ τ2
    typ-==-dec (τ1i ==> τ1o) (τ2i ==> τ2o)
      with typ-==-dec τ1i τ2i
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl
      with typ-==-dec τ1o τ2o
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl = Inl refl
    typ-==-dec (τ1i ==> τ1o) ⟨ _ ⟩ = Inr (λ ())
    typ-==-dec (τ1i ==> τ1o) D[ _ ] = Inr (λ ())
    typ-==-dec ⟨ τs1 ⟩ ⟨ τs2 ⟩
      with list<typ>-==-dec τs1 τs2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl = Inl refl
    typ-==-dec ⟨ _ ⟩ (_ ==> _) = Inr (λ ())
    typ-==-dec ⟨ _ ⟩ D[ _ ] = Inr (λ ())
    typ-==-dec D[ d1 ] D[ d2 ]
      with natEQ d1 d2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl = Inl refl
    typ-==-dec D[ _ ] (_ ==> _) = Inr (λ ())
    typ-==-dec D[ _ ] ⟨ _ ⟩ = Inr (λ ())
