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
    -- We define context decidability in contexts.agda,
    -- because it's an important metatheorem. However, it accepts a
    -- decidability theorem for its value type, and for environments that
    -- value type is result, so the termination checker complains. To fix
    -- this, we redefine type-specific versions of this theorem here.
    -- Note that we really should not be destructing contexts via `_::_` -
    -- here we only do that because we copied this code from the contexts file.

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

    ctx<rule>-==-dec : (rules1 rules2 : rule ctx) →
                        rules1 == rules2 ∨ rules1 ≠ rules2
    ctx<rule>-==-dec [] [] = Inl refl
    ctx<rule>-==-dec [] (_ :: _) = Inr (λ ())
    ctx<rule>-==-dec (_ :: _) [] = Inr (λ ())
    ctx<rule>-==-dec ((hx1 , hrule1) :: t1) ((hx2 , hrule2) :: t2)
      with natEQ hx1 hx2 | rule-==-dec hrule1 hrule2 | ctx<rule>-==-dec t1 t2
    ... | Inl refl | Inl refl | Inl refl = Inl refl
    ... | Inl refl | Inl refl | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl | Inr ne   | _        = Inr λ where refl → ne refl
    ... | Inr ne   | _        | _        = Inr λ where refl → ne refl

    rule-==-dec : (rule1 rule2 : rule) →
                   rule1 == rule2 ∨ rule1 ≠ rule2
    rule-==-dec (|C parm1 => branch1) (|C parm2 => branch2)
      with natEQ parm1 parm2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl
      with exp-==-dec branch1 branch2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl = Inl refl

    ex-==-dec : (ex1 ex2 : ex) →
                 ex1 == ex2 ∨ ex1 ≠ ex2
    ex-==-dec ⟨⟩ ⟨⟩ = Inl refl
    ex-==-dec ⟨⟩ ⟨ ex2 , ex3 ⟩ = Inr (λ ())
    ex-==-dec ⟨⟩ (C[ x ] ex2) = Inr (λ ())
    ex-==-dec ⟨⟩ ¿¿ = Inr (λ ())
    ex-==-dec ⟨⟩ (x ↦ ex2) = Inr (λ ())
    ex-==-dec ⟨ ex1a , ex1b ⟩ ⟨ ex2a , ex2b ⟩
      with ex-==-dec ex1a ex2a
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl
      with ex-==-dec ex1b ex2b
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    ex-==-dec ⟨ ex1 , ex2 ⟩ ⟨⟩ = Inr (λ ())
    ex-==-dec ⟨ _ , _ ⟩ (C[ _ ] _) = Inr (λ ())
    ex-==-dec ⟨ ex1 , ex2 ⟩ ¿¿ = Inr (λ ())
    ex-==-dec ⟨ ex1 , ex2 ⟩ (x ↦ ex3) = Inr (λ ())
    ex-==-dec (C[ c1 ] ex1) (C[ c2 ] ex2)
      with natEQ c1 c2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl
      with ex-==-dec ex1 ex2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    ex-==-dec (C[ x ] ex1) ⟨⟩ = Inr (λ ())
    ex-==-dec (C[ _ ] _) ⟨ _ , _ ⟩ = Inr (λ ())
    ex-==-dec (C[ x ] ex1) ¿¿ = Inr (λ ())
    ex-==-dec (C[ x ] ex1) (x₁ ↦ ex2) = Inr (λ ())
    ex-==-dec ¿¿ ¿¿ = Inl refl
    ex-==-dec ¿¿ ⟨⟩ = Inr (λ ())
    ex-==-dec ¿¿ ⟨ ex2 , ex3 ⟩ = Inr (λ ())
    ex-==-dec ¿¿ (C[ x ] ex2) = Inr (λ ())
    ex-==-dec ¿¿ (x ↦ ex2) = Inr (λ ())
    ex-==-dec (v1 ↦ ex1) (v2 ↦ ex2)
      with result-==-dec v1 v2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl
      with ex-==-dec ex1 ex2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    ex-==-dec (x ↦ ex1) ⟨⟩ = Inr (λ ())
    ex-==-dec (x ↦ ex1) ⟨ ex2 , ex3 ⟩ = Inr (λ ())
    ex-==-dec (x ↦ ex1) (C[ x₁ ] ex2) = Inr (λ ())
    ex-==-dec (x ↦ ex1) ¿¿ = Inr (λ ())

    exp-==-dec : (e1 e2 : exp) → e1 == e2 ∨ e1 ≠ e2
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
    exp-==-dec fix f1 ⦇·λ x1 => e1 ·⦈ X[ x ] = Inr (λ ())
    exp-==-dec fix f1 ⦇·λ x1 => e1 ·⦈ (e2 ∘ e3) = Inr (λ ())
    exp-==-dec fix f1 ⦇·λ x1 => e1 ·⦈ ⟨⟩ = Inr (λ ())
    exp-==-dec fix f1 ⦇·λ x1 => e1 ·⦈ ⟨ _ , _ ⟩ = Inr (λ ())
    exp-==-dec fix f1 ⦇·λ x1 => e1 ·⦈ (fst _) = Inr (λ ())
    exp-==-dec fix f1 ⦇·λ x1 => e1 ·⦈ (snd _) = Inr (λ ())
    exp-==-dec fix f1 ⦇·λ x1 => e1 ·⦈ (C[ x ] e2) = Inr (λ ())
    exp-==-dec fix f1 ⦇·λ x1 => e1 ·⦈ case e2 of⦃· x ·⦄ = Inr (λ ())
    exp-==-dec fix f1 ⦇·λ x1 => e1 ·⦈ ??[ x ] = Inr (λ ())
    exp-==-dec fix f1 ⦇·λ x1 => e1 ·⦈ (PBE:assert e2 e3) = Inr (λ ())
    exp-==-dec X[ x1 ] X[ x2 ]
      with natEQ x1 x2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    exp-==-dec X[ x1 ] fix x ⦇·λ x₁ => e2 ·⦈ = Inr (λ ())
    exp-==-dec X[ x1 ] (e2 ∘ e3) = Inr (λ ())
    exp-==-dec X[ x1 ] ⟨⟩ = Inr (λ ())
    exp-==-dec X[ x1 ] ⟨ _ , _ ⟩ = Inr (λ ())
    exp-==-dec X[ x1 ] (fst _) = Inr (λ ())
    exp-==-dec X[ x1 ] (snd _) = Inr (λ ())
    exp-==-dec X[ x1 ] (C[ x ] e2) = Inr (λ ())
    exp-==-dec X[ x1 ] case e2 of⦃· x ·⦄ = Inr (λ ())
    exp-==-dec X[ x1 ] ??[ x ] = Inr (λ ())
    exp-==-dec X[ x1 ] (PBE:assert e2 e3) = Inr (λ ())
    exp-==-dec (ef1 ∘ earg1) (ef2 ∘ earg2)
      with exp-==-dec ef1 ef2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl
      with exp-==-dec earg1 earg2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    exp-==-dec (ef1 ∘ earg1) fix x ⦇·λ x₁ => e2 ·⦈ = Inr (λ ())
    exp-==-dec (ef1 ∘ earg1) X[ x ] = Inr (λ ())
    exp-==-dec (ef1 ∘ earg1) ⟨⟩ = Inr (λ ())
    exp-==-dec (ef1 ∘ earg1) ⟨ _ , _ ⟩ = Inr (λ ())
    exp-==-dec (ef1 ∘ earg1) (fst _) = Inr (λ ())
    exp-==-dec (ef1 ∘ earg1) (snd _) = Inr (λ ())
    exp-==-dec (ef1 ∘ earg1) (C[ x ] e2) = Inr (λ ())
    exp-==-dec (ef1 ∘ earg1) case e2 of⦃· x ·⦄ = Inr (λ ())
    exp-==-dec (ef1 ∘ earg1) ??[ x ] = Inr (λ ())
    exp-==-dec (ef1 ∘ earg1) (PBE:assert e2 e3) = Inr (λ ())
    exp-==-dec ⟨⟩ ⟨⟩ = Inl refl
    exp-==-dec ⟨⟩ fix x ⦇·λ x₁ => e2 ·⦈ = Inr (λ ())
    exp-==-dec ⟨⟩ X[ x ] = Inr (λ ())
    exp-==-dec ⟨⟩ (e2 ∘ e3) = Inr (λ ())
    exp-==-dec ⟨⟩ ⟨ e2 , e3 ⟩ = Inr (λ ())
    exp-==-dec ⟨⟩ (fst e2) = Inr (λ ())
    exp-==-dec ⟨⟩ (snd e2) = Inr (λ ())
    exp-==-dec ⟨⟩ (C[ x ] e2) = Inr (λ ())
    exp-==-dec ⟨⟩ case e2 of⦃· x ·⦄ = Inr (λ ())
    exp-==-dec ⟨⟩ ??[ x ] = Inr (λ ())
    exp-==-dec ⟨⟩ (PBE:assert e2 e3) = Inr (λ ())
    exp-==-dec ⟨ es1a , es1b ⟩ ⟨ es2a , es2b ⟩
      with exp-==-dec es1a es2a
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl
      with exp-==-dec es1b es2b
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    exp-==-dec ⟨ _ , _ ⟩ fix x ⦇·λ x₁ => e2 ·⦈ = Inr (λ ())
    exp-==-dec ⟨ _ , _ ⟩ X[ x ] = Inr (λ ())
    exp-==-dec ⟨ _ , _ ⟩ (e2 ∘ e3) = Inr (λ ())
    exp-==-dec ⟨ _ , _ ⟩ ⟨⟩ = Inr (λ ())
    exp-==-dec ⟨ _ , _ ⟩ (fst _) = Inr (λ ())
    exp-==-dec ⟨ _ , _ ⟩ (snd _) = Inr (λ ())
    exp-==-dec ⟨ _ , _ ⟩ (C[ x ] e2) = Inr (λ ())
    exp-==-dec ⟨ _ , _ ⟩ case e2 of⦃· x ·⦄ = Inr (λ ())
    exp-==-dec ⟨ _ , _ ⟩ ??[ x ] = Inr (λ ())
    exp-==-dec ⟨ _ , _ ⟩ (PBE:assert e2 e3) = Inr (λ ())
    exp-==-dec (fst e1) (fst e2)
      with exp-==-dec e1 e2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    exp-==-dec (fst e1) fix x ⦇·λ x₁ => e2 ·⦈ = Inr (λ ())
    exp-==-dec (fst e1) X[ x ] = Inr (λ ())
    exp-==-dec (fst e1) (e2 ∘ e3) = Inr (λ ())
    exp-==-dec (fst e1) ⟨⟩ = Inr (λ ())
    exp-==-dec (fst e1) ⟨ e2 , e3 ⟩ = Inr (λ ())
    exp-==-dec (fst e1) (snd e2) = Inr (λ ())
    exp-==-dec (fst e1) (C[ x ] e2) = Inr (λ ())
    exp-==-dec (fst e1) case e2 of⦃· x ·⦄ = Inr (λ ())
    exp-==-dec (fst e1) ??[ x ] = Inr (λ ())
    exp-==-dec (fst e1) (PBE:assert e2 e3) = Inr (λ ())
    exp-==-dec (snd e1) (snd e2)
      with exp-==-dec e1 e2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    exp-==-dec (snd e1) fix x ⦇·λ x₁ => e2 ·⦈ = Inr (λ ())
    exp-==-dec (snd e1) X[ x ] = Inr (λ ())
    exp-==-dec (snd e1) (e2 ∘ e3) = Inr (λ ())
    exp-==-dec (snd e1) ⟨⟩ = Inr (λ ())
    exp-==-dec (snd e1) ⟨ e2 , e3 ⟩ = Inr (λ ())
    exp-==-dec (snd e1) (fst e2) = Inr (λ ())
    exp-==-dec (snd e1) (C[ x ] e2) = Inr (λ ())
    exp-==-dec (snd e1) case e2 of⦃· x ·⦄ = Inr (λ ())
    exp-==-dec (snd e1) ??[ x ] = Inr (λ ())
    exp-==-dec (snd e1) (PBE:assert e2 e3) = Inr (λ ())
    exp-==-dec (C[ c1 ] e1) (C[ c2 ] e2)
      with natEQ c1 c2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl
      with exp-==-dec e1 e2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    exp-==-dec (C[ c1 ] e1) fix x ⦇·λ x₁ => e2 ·⦈ = Inr (λ ())
    exp-==-dec (C[ c1 ] e1) X[ x ] = Inr (λ ())
    exp-==-dec (C[ c1 ] e1) (e2 ∘ e3) = Inr (λ ())
    exp-==-dec (C[ c1 ] e1) ⟨⟩ = Inr (λ ())
    exp-==-dec (C[ c1 ] e1) ⟨ _ , _ ⟩ = Inr (λ ())
    exp-==-dec (C[ c1 ] e1) (fst _) = Inr (λ ())
    exp-==-dec (C[ c1 ] e1) (snd _) = Inr (λ ())
    exp-==-dec (C[ c1 ] e1) case e2 of⦃· x ·⦄ = Inr (λ ())
    exp-==-dec (C[ c1 ] e1) ??[ x ] = Inr (λ ())
    exp-==-dec (C[ c1 ] e1) (PBE:assert e2 e3) = Inr (λ ())
    exp-==-dec case e1 of⦃· rules1 ·⦄ case e2 of⦃· rules2 ·⦄
      with exp-==-dec e1 e2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl
      with ctx<rule>-==-dec rules1 rules2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    exp-==-dec case e1 of⦃· rules1 ·⦄ fix x ⦇·λ x₁ => e2 ·⦈ = Inr (λ ())
    exp-==-dec case e1 of⦃· rules1 ·⦄ X[ x ] = Inr (λ ())
    exp-==-dec case e1 of⦃· rules1 ·⦄ (e2 ∘ e3) = Inr (λ ())
    exp-==-dec case e1 of⦃· rules1 ·⦄ ⟨⟩ = Inr (λ ())
    exp-==-dec case e1 of⦃· rules1 ·⦄ ⟨ _ , _ ⟩ = Inr (λ ())
    exp-==-dec case e1 of⦃· rules1 ·⦄ (fst _) = Inr (λ ())
    exp-==-dec case e1 of⦃· rules1 ·⦄ (snd _) = Inr (λ ())
    exp-==-dec case e1 of⦃· rules1 ·⦄ (C[ x ] e2) = Inr (λ ())
    exp-==-dec case e1 of⦃· rules1 ·⦄ ??[ x ] = Inr (λ ())
    exp-==-dec case e1 of⦃· rules1 ·⦄ (PBE:assert e2 e3) = Inr (λ ())
    exp-==-dec ??[ u1 ] ??[ u2 ]
      with natEQ u1 u2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    exp-==-dec ??[ u1 ] fix x ⦇·λ x₁ => e2 ·⦈ = Inr (λ ())
    exp-==-dec ??[ u1 ] X[ x ] = Inr (λ ())
    exp-==-dec ??[ u1 ] (e2 ∘ e3) = Inr (λ ())
    exp-==-dec ??[ u1 ] ⟨⟩ = Inr (λ ())
    exp-==-dec ??[ u1 ] ⟨ _ , _ ⟩ = Inr (λ ())
    exp-==-dec ??[ u1 ] (fst _) = Inr (λ ())
    exp-==-dec ??[ u1 ] (snd _) = Inr (λ ())
    exp-==-dec ??[ u1 ] (C[ x ] e2) = Inr (λ ())
    exp-==-dec ??[ u1 ] case e2 of⦃· x ·⦄ = Inr (λ ())
    exp-==-dec ??[ u1 ] (PBE:assert e2 e3) = Inr (λ ())
    exp-==-dec (PBE:assert e1a e1b) (PBE:assert e2a e2b)
      with exp-==-dec e1a e2a
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl
      with exp-==-dec e1b e2b
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    exp-==-dec (PBE:assert e1a e1b) fix x ⦇·λ x₁ => e2 ·⦈ = Inr (λ ())
    exp-==-dec (PBE:assert e1a e1b) X[ x ] = Inr (λ ())
    exp-==-dec (PBE:assert e1a e1b) (e2 ∘ e3) = Inr (λ ())
    exp-==-dec (PBE:assert e1a e1b) ⟨⟩ = Inr (λ ())
    exp-==-dec (PBE:assert e1a e1b) ⟨ _ , _ ⟩ = Inr (λ ())
    exp-==-dec (PBE:assert e1a e1b) (fst _) = Inr (λ ())
    exp-==-dec (PBE:assert e1a e1b) (snd _) = Inr (λ ())
    exp-==-dec (PBE:assert e1a e1b) (C[ x ] e2) = Inr (λ ())
    exp-==-dec (PBE:assert e1a e1b) case e2 of⦃· x ·⦄ = Inr (λ ())
    exp-==-dec (PBE:assert e1a e1b) ??[ x ] = Inr (λ ())

    result-==-dec : (r1 r2 : result) → r1 == r2 ∨ r1 ≠ r2
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
    result-==-dec [ E ]fix f ⦇·λ x => e ·⦈ ⟨⟩ = Inr (λ ())
    result-==-dec [ E ]fix f ⦇·λ x => e ·⦈ ⟨ _ , _ ⟩ = Inr (λ ())
    result-==-dec [ E ]fix f ⦇·λ x => e ·⦈ (C[ _ ] _) = Inr (λ ())
    result-==-dec [ x ]fix x₁ ⦇·λ x₂ => x₃ ·⦈ (C⁻[ x₄ ] r2) = Inr (λ ())
    result-==-dec [ E ]fix f ⦇·λ x => e ·⦈ [ _ ]??[ _ ] = Inr (λ ())
    result-==-dec [ E ]fix f ⦇·λ x => e ·⦈ (_ ∘ _) = Inr (λ ())
    result-==-dec [ E ]fix f ⦇·λ x => e ·⦈ (fst _) = Inr (λ ())
    result-==-dec [ E ]fix f ⦇·λ x => e ·⦈ (snd _) = Inr (λ ())
    result-==-dec [ E ]fix f ⦇·λ x => e ·⦈ [ _ ]case _ of⦃· _ ·⦄ = Inr (λ ())
    result-==-dec ⟨⟩ ⟨⟩ = Inl refl
    result-==-dec ⟨⟩ [ x ]fix x₁ ⦇·λ x₂ => x₃ ·⦈ = Inr (λ ())
    result-==-dec ⟨⟩ ⟨ r2 , r3 ⟩ = Inr (λ ())
    result-==-dec ⟨⟩ (C[ x ] r2) = Inr (λ ())
    result-==-dec ⟨⟩ (C⁻[ x ] r2) = Inr (λ ())
    result-==-dec ⟨⟩ [ x ]??[ x₁ ] = Inr (λ ())
    result-==-dec ⟨⟩ (r2 ∘ r3) = Inr (λ ())
    result-==-dec ⟨⟩ (fst r2) = Inr (λ ())
    result-==-dec ⟨⟩ (snd r2) = Inr (λ ())
    result-==-dec ⟨⟩ [ x ]case r2 of⦃· x₁ ·⦄ = Inr (λ ())
    result-==-dec ⟨ rs1a , rs1b ⟩ ⟨ rs2a , rs2b ⟩
      with result-==-dec rs1a rs2a
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl
      with result-==-dec rs1b rs2b
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl = Inl refl
    result-==-dec ⟨ _ , _ ⟩ [ _ ]fix _ ⦇·λ _ => _ ·⦈ = Inr (λ ())
    result-==-dec ⟨ _ , _ ⟩ ⟨⟩ = Inr (λ ())
    result-==-dec ⟨ _ , _ ⟩ (C[ _ ] _) = Inr (λ ())
    result-==-dec ⟨ _ , _ ⟩ (C⁻[ x ] r3) = Inr (λ ())
    result-==-dec ⟨ _ , _ ⟩ [ _ ]??[ _ ] = Inr (λ ())
    result-==-dec ⟨ _ , _ ⟩ (_ ∘ _) = Inr (λ ())
    result-==-dec ⟨ _ , _ ⟩ (snd _) = Inr (λ ())
    result-==-dec ⟨ _ , _ ⟩ (fst _) = Inr (λ ())
    result-==-dec ⟨ _ , _ ⟩ [ _ ]case _ of⦃· _ ·⦄ = Inr (λ ())
    result-==-dec (C[ c1 ] r1) (C[ c2 ] r2)
      with natEQ c1 c2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl
      with result-==-dec r1 r2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl = Inl refl
    result-==-dec (C[ c ] r) [ _ ]fix _ ⦇·λ _ => _ ·⦈ = Inr (λ ())
    result-==-dec (C[ c ] r) ⟨⟩ = Inr (λ ())
    result-==-dec (C[ c ] r) ⟨ _ , _ ⟩ = Inr (λ ())
    result-==-dec (C[ x ] r1) (C⁻[ x₁ ] r2) = Inr (λ ())
    result-==-dec (C[ c ] r) [ _ ]??[ _ ] = Inr (λ ())
    result-==-dec (C[ c ] r) (_ ∘ _) = Inr (λ ())
    result-==-dec (C[ c ] r) (fst _) = Inr (λ ())
    result-==-dec (C[ c ] r) (snd _) = Inr (λ ())
    result-==-dec (C[ c ] r) [ _ ]case _ of⦃· _ ·⦄ = Inr (λ ())
    result-==-dec (C⁻[ c1 ] r1) (C⁻[ c2 ] r2)
      with natEQ c1 c2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl
      with result-==-dec r1 r2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl = Inl refl
    result-==-dec (C⁻[ x ] r1) [ x₁ ]fix x₂ ⦇·λ x₃ => x₄ ·⦈ = Inr (λ ())
    result-==-dec (C⁻[ x ] r1) ⟨⟩ = Inr (λ ())
    result-==-dec (C⁻[ x ] r1) ⟨ r2 , r3 ⟩ = Inr (λ ())
    result-==-dec (C⁻[ x ] r1) (C[ x₁ ] r2) = Inr (λ ())
    result-==-dec (C⁻[ x ] r1) [ x₁ ]??[ x₂ ] = Inr (λ ())
    result-==-dec (C⁻[ x ] r1) (r2 ∘ r3) = Inr (λ ())
    result-==-dec (C⁻[ x ] r1) (fst r2) = Inr (λ ())
    result-==-dec (C⁻[ x ] r1) (snd r2) = Inr (λ ())
    result-==-dec (C⁻[ x ] r1) [ x₁ ]case r2 of⦃· x₂ ·⦄ = Inr (λ ())
    result-==-dec [ E1 ]??[ u1 ] [ E2 ]??[ u2 ]
      with ctx<result>-==-dec E1 E2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl
      with natEQ u1 u2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl = Inl refl
    result-==-dec [ E ]??[ u1 ] [ _ ]fix _ ⦇·λ _ => _ ·⦈ = Inr (λ ())
    result-==-dec [ E ]??[ u1 ] ⟨⟩ = Inr (λ ())
    result-==-dec [ E ]??[ u1 ] ⟨ _ , _ ⟩ = Inr (λ ())
    result-==-dec [ E ]??[ u1 ] (C[ _ ] _) = Inr (λ ())
    result-==-dec [ x ]??[ x₁ ] (C⁻[ x₂ ] r2) = Inr (λ ())
    result-==-dec [ E ]??[ u1 ] (_ ∘ _) = Inr (λ ())
    result-==-dec [ E ]??[ u1 ] (fst _) = Inr (λ ())
    result-==-dec [ E ]??[ u1 ] (snd _) = Inr (λ ())
    result-==-dec [ E ]??[ u1 ] [ _ ]case _ of⦃· _ ·⦄ = Inr (λ ())
    result-==-dec (rf1 ∘ rarg1) (rf2 ∘ rarg2)
      with result-==-dec rf1 rf2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl
      with result-==-dec rarg1 rarg2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl = Inl refl
    result-==-dec (rf ∘ rarg) [ _ ]fix _ ⦇·λ _ => _ ·⦈ = Inr (λ ())
    result-==-dec (rf ∘ rarg) ⟨⟩ = Inr (λ ())
    result-==-dec (rf ∘ rarg) ⟨ _ , _ ⟩ = Inr (λ ())
    result-==-dec (rf ∘ rarg) (C[ _ ] _) = Inr (λ ())
    result-==-dec (r1 ∘ r2) (C⁻[ x ] r3) = Inr (λ ())
    result-==-dec (rf ∘ rarg) [ _ ]??[ _ ] = Inr (λ ())
    result-==-dec (rf ∘ rarg) (fst _) = Inr (λ ())
    result-==-dec (rf ∘ rarg) (snd _) = Inr (λ ())
    result-==-dec (rf ∘ rarg) [ _ ]case _ of⦃· _ ·⦄ = Inr (λ ())
    result-==-dec (fst r1) (fst r2)
      with result-==-dec r1 r2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    result-==-dec (fst r1) [ x ]fix x₁ ⦇·λ x₂ => x₃ ·⦈ = Inr (λ ())
    result-==-dec (fst r1) ⟨⟩ = Inr (λ ())
    result-==-dec (fst r1) ⟨ r2 , r3 ⟩ = Inr (λ ())
    result-==-dec (fst r1) (C[ x ] r2) = Inr (λ ())
    result-==-dec (fst r1) (C⁻[ x ] r2) = Inr (λ ())
    result-==-dec (fst r1) [ x ]??[ x₁ ] = Inr (λ ())
    result-==-dec (fst r1) (r2 ∘ r3) = Inr (λ ())
    result-==-dec (fst r1) (snd r2) = Inr (λ ())
    result-==-dec (fst r1) [ x ]case r2 of⦃· x₁ ·⦄ = Inr (λ ())
    result-==-dec (snd r1) (snd r2)
      with result-==-dec r1 r2
    ... | Inr ne   = Inr (λ where refl → ne refl)
    ... | Inl refl = Inl refl
    result-==-dec (snd r1) [ x ]fix x₁ ⦇·λ x₂ => x₃ ·⦈ = Inr (λ ())
    result-==-dec (snd r1) ⟨⟩ = Inr (λ ())
    result-==-dec (snd r1) ⟨ r2 , r3 ⟩ = Inr (λ ())
    result-==-dec (snd r1) (C[ x ] r2) = Inr (λ ())
    result-==-dec (snd r1) (C⁻[ x ] r2) = Inr (λ ())
    result-==-dec (snd r1) [ x ]??[ x₁ ] = Inr (λ ())
    result-==-dec (snd r1) (r2 ∘ r3) = Inr (λ ())
    result-==-dec (snd r1) (fst r2) = Inr (λ ())
    result-==-dec (snd r1) [ x ]case r2 of⦃· x₁ ·⦄ = Inr (λ ())
    result-==-dec [ E1 ]case r1 of⦃· rules1 ·⦄ [ E2 ]case r2 of⦃· rules2 ·⦄
      with ctx<result>-==-dec E1 E2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl
      with result-==-dec r1 r2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl
      with ctx<rule>-==-dec rules1 rules2
    ... | Inr ne   = Inr λ where refl → ne refl
    ... | Inl refl = Inl refl
    result-==-dec [ E ]case r of⦃· rules ·⦄ [ _ ]fix _ ⦇·λ _ => _ ·⦈ = Inr (λ ())
    result-==-dec [ E ]case r of⦃· rules ·⦄ ⟨⟩ = Inr (λ ())
    result-==-dec [ E ]case r of⦃· rules ·⦄ ⟨ _ , _ ⟩ = Inr (λ ())
    result-==-dec [ E ]case r of⦃· rules ·⦄ (C[ _ ] _) = Inr (λ ())
    result-==-dec [ E ]case r of⦃· rules ·⦄ [ _ ]??[ _ ] = Inr (λ ())
    result-==-dec [ E ]case r of⦃· rules ·⦄ (_ ∘ _) = Inr (λ ())
    result-==-dec [ E ]case r of⦃· rules ·⦄ (fst _) = Inr (λ ())
    result-==-dec [ E ]case r of⦃· rules ·⦄ (snd _) = Inr (λ ())
    result-==-dec [ x ]case r1 of⦃· x₁ ·⦄ (C⁻[ x₂ ] r2) = Inr (λ ())

  typ-==-dec : (τ1 τ2 : typ) → τ1 == τ2 ∨ τ1 ≠ τ2
  typ-==-dec (τ1i ==> τ1o) (τ2i ==> τ2o)
    with typ-==-dec τ1i τ2i
  ... | Inr ne   = Inr λ where refl → ne refl
  ... | Inl refl
    with typ-==-dec τ1o τ2o
  ... | Inr ne   = Inr λ where refl → ne refl
  ... | Inl refl = Inl refl
  typ-==-dec (τ1i ==> τ1o) ⟨⟩ = Inr (λ ())
  typ-==-dec (τ1i ==> τ1o) ⟨ _ × _ ⟩ = Inr (λ ())
  typ-==-dec (τ1i ==> τ1o) D[ _ ] = Inr (λ ())
  typ-==-dec ⟨⟩ ⟨⟩ = Inl refl
  typ-==-dec ⟨⟩ ⟨ τ2 × τ3 ⟩ = Inr (λ ())
  typ-==-dec ⟨⟩ (_ ==> _) = Inr (λ ())
  typ-==-dec ⟨⟩ D[ _ ] = Inr (λ ())
  typ-==-dec ⟨ τ1a × τ1b ⟩ ⟨ τ2a × τ2b ⟩
    with typ-==-dec τ1a τ2a
  ... | Inr ne   = Inr λ where refl → ne refl
  ... | Inl refl
    with typ-==-dec τ1b τ2b
  ... | Inr ne   = Inr λ where refl → ne refl
  ... | Inl refl = Inl refl
  typ-==-dec ⟨ τ1 × τ2 ⟩ ⟨⟩ = Inr (λ ())
  typ-==-dec ⟨ _ × _ ⟩ (_ ==> _) = Inr (λ ())
  typ-==-dec ⟨ _ × _ ⟩ D[ _ ] = Inr (λ ())
  typ-==-dec D[ d1 ] D[ d2 ]
    with natEQ d1 d2
  ... | Inr ne   = Inr λ where refl → ne refl
  ... | Inl refl = Inl refl
  typ-==-dec D[ _ ] (_ ==> _) = Inr (λ ())
  typ-==-dec D[ _ ] ⟨⟩ = Inr (λ ())
  typ-==-dec D[ _ ] ⟨ _ × _ ⟩ = Inr (λ ())

  final-dec : ∀{r} → r final ∨ (r final → ⊥)

  env-final-dec : ∀{E} → E env-final ∨ (E env-final → ⊥)

  final-dec {[ E ]fix x₁ ⦇·λ x₂ => e ·⦈}
    with env-final-dec {E}
  ... | Inr nf  = Inr (λ {(FFix f) → nf f})
  ... | Inl E-f = Inl (FFix E-f)
  final-dec {⟨⟩} = Inl FUnit
  final-dec {⟨ r1 , r2 ⟩}
    with final-dec {r1}
  ... | Inr nf   = Inr λ {(FPair h1 h2) → nf h1}
  ... | Inl r1-f
    with final-dec {r2}
  ... | Inr nf   = Inr λ {(FPair h1 h2) → nf h2}
  ... | Inl r2-f = Inl (FPair r1-f r2-f)
  final-dec {C[ x ] r}
    with final-dec {r}
  ... | Inr nf  = Inr λ {(FCon h1) → nf h1}
  ... | Inl r-f = Inl (FCon r-f)
  final-dec {C⁻[ x ] r} = Inr (λ ())
  final-dec {[ E ]??[ x₁ ]}
    with env-final-dec {E}
  ... | Inr nf  = Inr λ {(FHole h1) → nf h1}
  ... | Inl E-f = Inl (FHole E-f)
  final-dec {r1 ∘ r2}
    with final-dec {r1}
  ... | Inr nf   = Inr λ {(FAp h _ _) → nf h}
  ... | Inl r1-f
    with final-dec {r2}
  ... | Inr nf   = Inr λ {(FAp _ h _) → nf h}
  final-dec {[ x ]fix x₁ ⦇·λ x₂ => x₃ ·⦈ ∘ r2} | Inl r1-f | Inl r2-f
    = Inr λ {(FAp _ _ h) → abort (h refl)}
  final-dec {⟨⟩ ∘ r2} | Inl r1-f | Inl r2-f = Inl (FAp r1-f r2-f (λ {E} {f} {x} {e} ()))
  final-dec {⟨ r1 , r3 ⟩ ∘ r2} | Inl r1-f | Inl r2-f = Inl (FAp r1-f r2-f (λ {E} {f} {x} {e} ()))
  final-dec {(C[ x ] r1) ∘ r2} | Inl r1-f | Inl r2-f = Inl (FAp r1-f r2-f (λ {E} {f} {x} {e} ()))
  final-dec {[ x ]??[ x₁ ] ∘ r2} | Inl r1-f | Inl r2-f = Inl (FAp r1-f r2-f  (λ {E} {f} {x} {e} ()))
  final-dec {(r1 ∘ r3) ∘ r2} | Inl r1-f | Inl r2-f = Inl (FAp r1-f r2-f (λ {E} {f} {x} {e} ()))
  final-dec {fst r1 ∘ r2} | Inl r1-f | Inl r2-f = Inl (FAp r1-f r2-f (λ {E} {f} {x} {e} ()))
  final-dec {snd r1 ∘ r2} | Inl r1-f | Inl r2-f = Inl (FAp r1-f r2-f (λ {E} {f} {x} {e} ()))
  final-dec {[ x ]case r1 of⦃· x₁ ·⦄ ∘ r2} | Inl r1-f | Inl r2-f = Inl (FAp r1-f r2-f (λ {E} {f} {x} {e} ()))
  final-dec {fst r}
    with final-dec {r}
  ... | Inr nf  = Inr λ {(FFst h _) → nf h}
  final-dec {fst ⟨ r , r₁ ⟩} | Inl r-f
    = Inr λ {(FFst _ h) → abort (h refl)}
  final-dec {fst [ x ]fix x₁ ⦇·λ x₂ => x₃ ·⦈} | Inl r-f = Inl (FFst r-f (λ {r1} {r2} ()))
  final-dec {fst ⟨⟩} | Inl r-f = Inl (FFst r-f (λ {r1} {r2} ()))
  final-dec {fst (C[ x ] r)} | Inl r-f = Inl (FFst r-f (λ {r1} {r2} ()))
  final-dec {fst [ x ]??[ x₁ ]} | Inl r-f = Inl (FFst r-f (λ {r1} {r2} ()))
  final-dec {fst (r ∘ r₁)} | Inl r-f = Inl (FFst r-f (λ {r1} {r2} ()))
  final-dec {fst (fst r)} | Inl r-f = Inl (FFst r-f (λ {r1} {r2} ()))
  final-dec {fst (snd r)} | Inl r-f = Inl (FFst r-f (λ {r1} {r2} ()))
  final-dec {fst [ x ]case r of⦃· x₁ ·⦄} | Inl r-f = Inl (FFst r-f (λ {r1} {r2} ()))
  final-dec {snd r}
    with final-dec {r}
  ... | Inr nf  = Inr λ {(FSnd h _) → nf h}
  final-dec {snd ⟨ r , r₁ ⟩} | Inl r-f
    = Inr λ {(FSnd _ h) → abort (h refl)}
  final-dec {snd [ x ]fix x₁ ⦇·λ x₂ => x₃ ·⦈} | Inl r-f = Inl (FSnd r-f (λ {r1} {r2} ()))
  final-dec {snd ⟨⟩} | Inl r-f = Inl (FSnd r-f (λ {r1} {r2} ()))
  final-dec {snd (C[ x ] r)} | Inl r-f = Inl (FSnd r-f (λ {r1} {r2} ()))
  final-dec {snd [ x ]??[ x₁ ]} | Inl r-f = Inl (FSnd r-f (λ {r1} {r2} ()))
  final-dec {snd (r ∘ r₁)} | Inl r-f = Inl (FSnd r-f (λ {r1} {r2} ()))
  final-dec {snd (fst r)} | Inl r-f = Inl (FSnd r-f (λ {r1} {r2} ()))
  final-dec {snd (snd r)} | Inl r-f = Inl (FSnd r-f (λ {r1} {r2} ()))
  final-dec {snd [ x ]case r of⦃· x₁ ·⦄} | Inl r-f = Inl (FSnd r-f (λ {r1} {r2} ()))
  final-dec {[ E ]case r of⦃· x₁ ·⦄}
    with final-dec {r}
  ... | Inr nf  = Inr λ {(FCase h _ _) → nf h}
  ... | Inl r-f
    with env-final-dec {E}
  ... | Inr nf  = Inr λ {(FCase _ _ h) → nf h}
  final-dec {[ E ]case C[ x ] r of⦃· x₁ ·⦄} | Inl r-f | Inl E-f
    = Inr λ {(FCase _ h _) → abort (h refl)}
  final-dec {[ E ]case [ x ]fix x₂ ⦇·λ x₃ => x₄ ·⦈ of⦃· x₁ ·⦄} | Inl r-f | Inl E-f = Inl (FCase r-f (λ {c} {r'} ()) E-f)
  final-dec {[ E ]case ⟨⟩ of⦃· x₁ ·⦄} | Inl r-f | Inl E-f = Inl (FCase r-f (λ {c} {r'} ()) E-f)
  final-dec {[ E ]case ⟨ r , r₁ ⟩ of⦃· x₁ ·⦄} | Inl r-f | Inl E-f = Inl (FCase r-f (λ {c} {r'} ()) E-f)
  final-dec {[ E ]case [ x ]??[ x₂ ] of⦃· x₁ ·⦄} | Inl r-f | Inl E-f = Inl (FCase r-f (λ {c} {r'} ()) E-f)
  final-dec {[ E ]case r ∘ r₁ of⦃· x₁ ·⦄} | Inl r-f | Inl E-f = Inl (FCase r-f (λ {c} {r'} ()) E-f)
  final-dec {[ E ]case fst r of⦃· x₁ ·⦄} | Inl r-f | Inl E-f = Inl (FCase r-f (λ {c} {r'} ()) E-f)
  final-dec {[ E ]case snd r of⦃· x₁ ·⦄} | Inl r-f | Inl E-f = Inl (FCase r-f (λ {c} {r'} ()) E-f)
  final-dec {[ E ]case [ x ]case r of⦃· x₂ ·⦄ of⦃· x₁ ·⦄} | Inl r-f | Inl E-f = Inl (FCase r-f (λ {c} {r'} ()) E-f)

  env-final-dec {[]} = Inl (EF (λ ()))
  env-final-dec {(_ , r) :: E}
    with final-dec {r}
  ... | Inr nf       = Inr (λ {(EF h) → nf (h InH)})
  ... | Inl r-f
    with env-final-dec {E}
  ... | Inr nf       = Inr (λ {(EF h) → nf (EF (λ z → h (InT z)))})
  ... | Inl (EF E-f) = Inl (EF λ {InH → r-f ; (InT h) → E-f h})

  Coerce-dec : ∀{r} → Σ[ ex ∈ ex ] (Coerce r := ex) ∨ (Σ[ ex ∈ ex ] (Coerce r := ex) → ⊥)
  Coerce-dec {[ x ]fix x₁ ⦇·λ x₂ => x₃ ·⦈} = Inr (λ where (_ , ()))
  Coerce-dec {⟨⟩} = Inl (⟨⟩ , CoerceUnit)
  Coerce-dec {⟨ r1 , r2 ⟩}
    with Coerce-dec {r1}
  ...  | Inr nc          = Inr λ {(_ , CoercePair c-r1 _) → nc (_ , c-r1)}
  ...  | Inl (_ , c-r1)
    with Coerce-dec {r2}
  ...  | Inr nc          = Inr λ {(_ , CoercePair _ c-r2) → nc (_ , c-r2)}
  ...  | Inl (_ , c-r2)  = Inl (_ , CoercePair c-r1 c-r2)
  Coerce-dec {C[ c ] r}
    with Coerce-dec {r}
  ...  | Inr nc         = Inr λ {(_ , CoerceCtor c-r) → nc (_ , c-r)}
  ...  | Inl (_ , c-r)  = Inl (_ , CoerceCtor c-r)
  Coerce-dec {C⁻[ x ] r} = Inr (λ where (_ , ()))
  Coerce-dec {[ x ]??[ x₁ ]} = Inr (λ where (_ , ()))
  Coerce-dec {r ∘ r₁} = Inr (λ where (_ , ()))
  Coerce-dec {fst r} = Inr (λ where (_ , ()))
  Coerce-dec {snd r} = Inr (λ where (_ , ()))
  Coerce-dec {[ x ]case r of⦃· x₁ ·⦄} = Inr (λ where (_ , ()))

  value-dec : ∀{r} → r value ∨ (r value → ⊥)
  value-dec {[ E ]fix x₁ ⦇·λ x₂ => x₃ ·⦈}
    with env-final-dec {E}
  ... | Inr nf  = Inr (λ {(VFix E-f) → nf E-f})
  ... | Inl E-f = Inl (VFix E-f)
  value-dec {⟨⟩} = Inl VUnit
  value-dec {⟨ r1 , r2 ⟩}
    with value-dec {r1}
  ... | Inr nv  = Inr λ {(VPair h _) → nv h}
  ... | Inl r1v
    with value-dec {r2}
  ... | Inr nv  = Inr λ {(VPair _ h) → nv h}
  ... | Inl r2v = Inl (VPair r1v r2v)
  value-dec {C[ x ] r}
    with value-dec {r}
  ... | Inl rv = Inl (VCon rv)
  ... | Inr nv = Inr (λ {(VCon rv) → nv rv})
  value-dec {C⁻[ x ] r} = Inr (λ ())
  value-dec {[ x ]??[ x₁ ]} = Inr (λ ())
  value-dec {r ∘ r₁} = Inr (λ ())
  value-dec {fst r} = Inr (λ ())
  value-dec {snd r} = Inr (λ ())
  value-dec {[ x ]case r of⦃· x₁ ·⦄} = Inr (λ ())

  ex-¿¿-dec : ∀{ex} → ex == ¿¿ ∨ ex ≠ ¿¿
  ex-¿¿-dec {⟨⟩} = Inr (λ ())
  ex-¿¿-dec {⟨ ex₁ , ex₂ ⟩} = Inr (λ ())
  ex-¿¿-dec {C[ x ] ex₁} = Inr (λ ())
  ex-¿¿-dec {¿¿} = Inl refl
  ex-¿¿-dec {x ↦ ex₁} = Inr (λ ())
