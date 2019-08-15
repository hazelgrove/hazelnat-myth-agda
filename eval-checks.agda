open import Nat
open import Prelude
open import List

open import contexts
open import core

open import lemmas-general
open import preservation

module eval-checks where
  eval-unicity : ∀{⛽ Δ Σ' Γ E e τ r r' K K'} →
                   Δ , Σ' , Γ ⊢ E →
                   Δ , Σ' , Γ ⊢ e :: τ →
                   E ⊢ e ⌊ ⛽ ⌋⇒ r ⊣ K →
                   E ⊢ e ⌊ ⛽ ⌋⇒ r' ⊣ K' →
                   r == r' ∧ K == K'

  xc-unicity : ∀{Δ Σ' r1 r2 τ K K'} →
                 Δ , Σ' ⊢ r1 ·: τ →
                 Δ , Σ' ⊢ r2 ·: τ →
                 Constraints⦃ r1 , r2 ⦄:= K →
                 Constraints⦃ r1 , r2 ⦄:= K' →
                 K == K'

  eval-unicity Γ⊢E (TAFix _) EFix EFix = refl , refl
  eval-unicity Γ⊢E (TAVar _) (EVar h) (EVar h') = ctxunicity h h' , refl
  eval-unicity Γ⊢E (TAApp _ ta-f ta-arg) (EAppFix f1 form eval-f eval-arg eval) (EAppFix f2 form' eval-f' eval-arg' eval')
    rewrite form | form'
    with eval-unicity Γ⊢E ta-f eval-f eval-f' | eval-unicity Γ⊢E ta-arg eval-arg eval-arg'
  ... | refl , refl | refl , refl
    with preservation Γ⊢E ta-f eval-f
  ... | TAFix Γ'⊢Ef (TAFix ta-ef)
    rewrite Fuel-depletion-unicity f1 f2
    with eval-unicity (EnvInd (EnvInd Γ'⊢Ef (preservation Γ⊢E ta-f eval-f)) (preservation Γ⊢E ta-arg eval-arg)) ta-ef eval eval'
  ... | refl , refl = refl , refl
  eval-unicity Γ⊢E TAUnit EUnit EUnit = refl , refl
  eval-unicity Γ⊢E (TAApp x ta-e ta-e₁) (EAppFix x₁ form eval eval₁ eval₂) (EAppUnfinished eval' nf eval'')
    with eval-unicity Γ⊢E ta-e eval eval'
  ... | refl , refl
    rewrite form
      = abort (nf refl)
  eval-unicity Γ⊢E (TAApp x ta-e ta-e₁) (EAppUnfinished eval nf eval₁) (EAppFix x₂ form eval' eval'' eval''')
    with eval-unicity Γ⊢E ta-e eval eval'
  ... | refl , refl
    rewrite form
      = abort (nf refl)
  eval-unicity Γ⊢E (TAApp x ta-f ta-arg) (EAppUnfinished eval-f x₁ eval-arg) (EAppUnfinished eval-f' x₂ eval-arg')
    with eval-unicity Γ⊢E ta-f eval-f eval-f' | eval-unicity Γ⊢E ta-arg eval-arg eval-arg'
  ... | refl , refl | refl , refl = refl , refl
  eval-unicity Γ⊢E (TAPair x ta-e1 ta-e2) (EPair eval1 eval2) (EPair eval1' eval2')
    with eval-unicity Γ⊢E ta-e1 eval1 eval1' | eval-unicity Γ⊢E ta-e2 eval2 eval2'
  ... | refl , refl | refl , refl = refl , refl
  eval-unicity Γ⊢E (TAFst ta-e) (EFst eval) (EFst eval')
    with eval-unicity Γ⊢E ta-e eval eval'
  ... | refl , refl = refl , refl
  eval-unicity Γ⊢E (TAFst ta-e) (EFst eval) (EFstUnfinished eval' np)
    with eval-unicity Γ⊢E ta-e eval eval'
  ... | refl , refl = abort (np refl)
  eval-unicity Γ⊢E (TAFst ta-e) (EFstUnfinished eval np) (EFst eval')
    with eval-unicity Γ⊢E ta-e eval eval'
  ... | refl , refl = abort (np refl)
  eval-unicity Γ⊢E (TAFst ta-e) (EFstUnfinished eval x) (EFstUnfinished eval' x₁)
    with eval-unicity Γ⊢E ta-e eval eval'
  ... | refl , refl = refl , refl
  eval-unicity Γ⊢E (TASnd ta-e) (ESnd eval) (ESnd eval')
    with eval-unicity Γ⊢E ta-e eval eval'
  ... | refl , refl = refl , refl
  eval-unicity Γ⊢E (TASnd ta-e) (ESnd eval) (ESndUnfinished eval' np)
    with eval-unicity Γ⊢E ta-e eval eval'
  ... | refl , refl = abort (np refl)
  eval-unicity Γ⊢E (TASnd ta-e) (ESndUnfinished eval np) (ESnd eval')
    with eval-unicity Γ⊢E ta-e eval eval'
  ... | refl , refl = abort (np refl)
  eval-unicity Γ⊢E (TASnd ta-e) (ESndUnfinished eval x) (ESndUnfinished eval' x₁)
    with eval-unicity Γ⊢E ta-e eval eval'
  ... | refl , refl = refl , refl
  eval-unicity Γ⊢E (TACtor x x₁ ta-e) (ECtor eval) (ECtor eval')
    with eval-unicity Γ⊢E ta-e eval eval'
  ... | refl , refl = refl , refl
  eval-unicity Γ⊢E (TACase d∈σ' ta-e x₁ ta-rules) (EMatch f1 form eval-e eval-ec) (EMatch f2 form' eval'-e eval'-ec)
    with eval-unicity Γ⊢E ta-e eval-e eval'-e
  ... | refl , refl
    with ctxunicity form form'
  ... | refl
    with ta-rules form
  ... | _ , _ , _ , c∈cctx , ta-ec
    with preservation Γ⊢E ta-e eval-e
  ... | TACtor d∈'σ' c∈'cctx ta-r'
    rewrite ctxunicity d∈σ' d∈'σ' | ctxunicity c∈cctx c∈'cctx | Fuel-depletion-unicity f1 f2
    with eval-unicity (EnvInd Γ⊢E ta-r') ta-ec eval-ec eval'-ec
  ... | refl , refl = refl , refl
  eval-unicity Γ⊢E (TACase x ta-e x₁ x₂) (EMatch x₃ x₄ eval eval₁) (EMatchUnfinished eval' nc)
    with eval-unicity Γ⊢E ta-e eval eval'
  ... | refl , refl = abort (nc refl)
  eval-unicity Γ⊢E (TACase x ta-e x₁ x₂) (EMatchUnfinished eval nc) (EMatch x₄ x₅ eval' eval'')
    with eval-unicity Γ⊢E ta-e eval eval'
  ... | refl , refl = abort (nc refl)
  eval-unicity Γ⊢E (TACase x ta-e x₁ x₂) (EMatchUnfinished eval x₃) (EMatchUnfinished eval' x₄)
    with eval-unicity Γ⊢E ta-e eval eval'
  ... | refl , refl = refl , refl
  eval-unicity Γ⊢E (TAHole x) EHole EHole = refl , refl
  eval-unicity Γ⊢E (TAAsrt x ta-e1 ta-e2) (EAsrt eval1 eval2 xc) (EAsrt eval1' eval2' xc')
    with eval-unicity Γ⊢E ta-e1 eval1 eval1' | eval-unicity Γ⊢E ta-e2 eval2 eval2'
  ... | refl , refl | refl , refl
    rewrite xc-unicity (preservation Γ⊢E ta-e1 eval1) (preservation Γ⊢E ta-e2 eval2) xc xc'
      = refl , refl

  xc-unicity ta1 ta2 RCRefl RCRefl = refl
  xc-unicity ta1 ta2 RCRefl (RCPair x rc2 rc3) = abort (x refl)
  xc-unicity ta1 ta2 RCRefl (RCCtor x rc2) = abort (x refl)
  xc-unicity ta1 ta2 RCRefl (RCVal1 x x₁ x₂ x₃) = abort (x refl)
  xc-unicity ta1 ta2 RCRefl (RCVal2 x x₁ x₂ x₃) = abort (x refl)
  xc-unicity ta1 ta2 (RCPair x rc1 rc2) RCRefl = abort (x refl)
  xc-unicity (TAPair ta1 ta2) (TAPair ta3 ta4) (RCPair x rc1 rc2) (RCPair x₁ rc3 rc4)
    rewrite xc-unicity ta1 ta3 rc1 rc3 | xc-unicity ta2 ta4 rc2 rc4
      = refl
  xc-unicity ta1 ta2 (RCPair x rc1 rc2) (RCVal1 x₁ (Inl x₂) x₃ x₄) = abort (x₂ refl)
  xc-unicity ta1 ta2 (RCPair x rc1 rc2) (RCVal1 x₁ (Inr x₂) x₃ x₄) = abort (x₂ refl)
  xc-unicity ta1 ta2 (RCPair x rc1 rc2) (RCVal2 x₁ (Inl x₂) x₃ x₄) = abort (x₂ refl)
  xc-unicity ta1 ta2 (RCPair x rc1 rc2) (RCVal2 x₁ (Inr x₂) x₃ x₄) = abort (x₂ refl)
  xc-unicity ta1 ta2 (RCCtor x rc1) RCRefl = abort (x refl)
  xc-unicity (TACtor d∈σ' c∈cctx ta1) (TACtor d∈'σ' c∈'cctx ta2) (RCCtor x rc1) (RCCtor x₁ rc2)
    rewrite ctxunicity d∈σ' d∈'σ' | ctxunicity c∈cctx c∈'cctx
      = xc-unicity ta1 ta2 rc1 rc2
  xc-unicity ta1 ta2 (RCCtor x rc1) (RCVal1 x₁ x₂ (Inl x₃) x₄) = abort (x₃ refl)
  xc-unicity ta1 ta2 (RCCtor x rc1) (RCVal1 x₁ x₂ (Inr x₃) x₄) = abort (x₃ refl)
  xc-unicity ta1 ta2 (RCCtor x rc1) (RCVal2 x₁ x₂ (Inl x₃) x₄) = abort (x₃ refl)
  xc-unicity ta1 ta2 (RCCtor x rc1) (RCVal2 x₁ x₂ (Inr x₃) x₄) = abort (x₃ refl)
  xc-unicity ta1 ta2 (RCVal1 x x₁ x₂ x₃) RCRefl = abort (x refl)
  xc-unicity ta1 ta2 (RCVal1 x (Inl x₁) x₂ x₃) (RCPair x₄ rc2 rc3) = abort (x₁ refl)
  xc-unicity ta1 ta2 (RCVal1 x (Inr x₁) x₂ x₃) (RCPair x₄ rc2 rc3) = abort (x₁ refl)
  xc-unicity ta1 ta2 (RCVal1 x _ (Inl x₁) x₃) (RCCtor x₄ rc2) = abort (x₁ refl)
  xc-unicity ta1 ta2 (RCVal1 x _ (Inr x₁) x₃) (RCCtor x₄ rc2) = abort (x₁ refl)
  xc-unicity ta1 ta2 (RCVal1 x x₁ x₂ x₃) (RCVal1 x₄ x₅ x₆ x₇)
    rewrite Coerce-unicity x₃ x₇
      = refl
  xc-unicity TAUnit TAUnit (RCVal1 x x₁ x₂ x₃) (RCVal2 x₄ x₅ x₆ x₇) = abort (x₄ refl)
  xc-unicity (TAPair ta1 ta2) (TAPair ta3 ta4) (RCVal1 x (Inl x₂) _ x₃) (RCVal2 x₄ x₅ x₆ x₇) = abort (x₂ refl)
  xc-unicity (TAPair ta1 ta2) (TAPair ta3 ta4) (RCVal1 x (Inr x₂) _ x₃) (RCVal2 x₄ x₅ x₆ x₇) = abort (x₂ refl)
  xc-unicity (TACtor x₈ x₉ ta1) (TACtor x₁₀ x₁₁ ta2) (RCVal1 x x₁ (Inl h) x₃) (RCVal2 x₄ x₅ x₆ x₇) = abort (h refl)
  xc-unicity (TACtor x₈ x₉ ta1) (TACtor x₁₀ x₁₁ ta2) (RCVal1 x x₁ (Inr h) x₃) (RCVal2 x₄ x₅ x₆ x₇) = abort (h refl)
  xc-unicity ta1 ta2 (RCVal2 x x₁ x₂ x₃) RCRefl = abort (x refl)
  xc-unicity ta1 ta2 (RCVal2 x (Inl x₁) x₂ x₃) (RCPair x₄ rc2 rc3) = abort (x₁ refl)
  xc-unicity ta1 ta2 (RCVal2 x (Inr x₁) x₂ x₃) (RCPair x₄ rc2 rc3) = abort (x₁ refl)
  xc-unicity ta1 ta2 (RCVal2 x x₁ (Inl x₂) x₃) (RCCtor x₄ rc2) = abort (x₂ refl)
  xc-unicity ta1 ta2 (RCVal2 x x₁ (Inr x₂) x₃) (RCCtor x₄ rc2) = abort (x₂ refl)
  xc-unicity TAUnit TAUnit (RCVal2 x x₁ x₂ x₃) (RCVal1 x₄ x₅ x₆ x₇) = abort (x refl)
  xc-unicity (TAPair ta1 ta2) (TAPair ta3 ta4) (RCVal2 x (Inl h) x₂ x₃) (RCVal1 x₄ x₅ x₆ x₇) = abort (h refl)
  xc-unicity (TAPair ta1 ta2) (TAPair ta3 ta4) (RCVal2 x (Inr h) x₂ x₃) (RCVal1 x₄ x₅ x₆ x₇) = abort (h refl)
  xc-unicity (TACtor x₈ x₉ ta1) (TACtor x₁₀ x₁₁ ta2) (RCVal2 x x₁ (Inl h) x₃) (RCVal1 x₄ x₅ x₆ x₇) = abort (h refl)
  xc-unicity (TACtor x₈ x₉ ta1) (TACtor x₁₀ x₁₁ ta2) (RCVal2 x x₁ (Inr h) x₃) (RCVal1 x₄ x₅ x₆ x₇) = abort (h refl)
  xc-unicity ta1 ta2 (RCVal2 x x₁ x₂ x₃) (RCVal2 x₄ x₅ x₆ x₇)
    rewrite Coerce-unicity x₃ x₇
      = refl

  -- useful in practice, since threading type-checks around everywhere can be a pain
  -- note that this does not prove unicity of constraints, which isn't true for poorly-typed terms
  untyped-eval-unicity : ∀{⛽ E e r r' K K'} →
                           E ⊢ e ⌊ ⛽ ⌋⇒ r ⊣ K →
                           E ⊢ e ⌊ ⛽ ⌋⇒ r' ⊣ K' →
                           r == r'
  untyped-eval-unicity EFix EFix = refl
  untyped-eval-unicity (EVar h) (EVar h') = ctxunicity h h'
  untyped-eval-unicity (EAppFix f1 form eval-f eval-arg eval) (EAppFix f2 form' eval-f' eval-arg' eval')
    rewrite form | form'
    with untyped-eval-unicity eval-f eval-f' | untyped-eval-unicity eval-arg eval-arg'
  ... | refl | refl
    rewrite Fuel-depletion-unicity f1 f2 | untyped-eval-unicity eval eval'
      = refl
  untyped-eval-unicity EUnit EUnit = refl
  untyped-eval-unicity (EAppFix x₁ form eval eval₁ eval₂) (EAppUnfinished eval' nf eval'')
    rewrite untyped-eval-unicity eval eval' | form
      = abort (nf refl)
  untyped-eval-unicity (EAppUnfinished eval nf eval₁) (EAppFix x₂ form eval' eval'' eval''')
    rewrite untyped-eval-unicity eval eval' | form
      = abort (nf refl)
  untyped-eval-unicity (EAppUnfinished eval-f x₁ eval-arg) (EAppUnfinished eval-f' x₂ eval-arg')
    rewrite untyped-eval-unicity eval-f eval-f' | untyped-eval-unicity eval-arg eval-arg'
      = refl
  untyped-eval-unicity (EPair eval1 eval2) (EPair eval1' eval2')
    rewrite untyped-eval-unicity eval1 eval1' | untyped-eval-unicity eval2 eval2'
      = refl
  untyped-eval-unicity (EFst eval) (EFst eval')
    with untyped-eval-unicity eval eval'
  ... | refl = refl
  untyped-eval-unicity (EFst eval) (EFstUnfinished eval' np)
    with untyped-eval-unicity eval eval'
  ... | refl = abort (np refl)
  untyped-eval-unicity (EFstUnfinished eval np) (EFst eval')
    with untyped-eval-unicity eval eval'
  ... | refl = abort (np refl)
  untyped-eval-unicity (EFstUnfinished eval x) (EFstUnfinished eval' x₁)
    with untyped-eval-unicity eval eval'
  ... | refl = refl
  untyped-eval-unicity (ESnd eval) (ESnd eval')
    with untyped-eval-unicity eval eval'
  ... | refl = refl
  untyped-eval-unicity (ESnd eval) (ESndUnfinished eval' np)
    with untyped-eval-unicity eval eval'
  ... | refl = abort (np refl)
  untyped-eval-unicity (ESndUnfinished eval np) (ESnd eval')
    with untyped-eval-unicity eval eval'
  ... | refl = abort (np refl)
  untyped-eval-unicity (ESndUnfinished eval x) (ESndUnfinished eval' x₁)
    with untyped-eval-unicity eval eval'
  ... | refl = refl
  untyped-eval-unicity (ECtor eval) (ECtor eval')
    with untyped-eval-unicity eval eval'
  ... | refl = refl
  untyped-eval-unicity (EMatch f1 form eval-e eval-ec) (EMatch f2 form' eval'-e eval'-ec)
    with untyped-eval-unicity eval-e eval'-e
  ... | refl
    with ctxunicity form form'
  ... | refl
    rewrite Fuel-depletion-unicity f1 f2
    with untyped-eval-unicity eval-ec eval'-ec
  ... | refl = refl
  untyped-eval-unicity (EMatch x₃ x₄ eval eval₁) (EMatchUnfinished eval' nc)
    with untyped-eval-unicity eval eval'
  ... | refl = abort (nc refl)
  untyped-eval-unicity (EMatchUnfinished eval nc) (EMatch x₄ x₅ eval' eval'')
    with untyped-eval-unicity eval eval'
  ... | refl = abort (nc refl)
  untyped-eval-unicity (EMatchUnfinished eval x₃) (EMatchUnfinished eval' x₄)
    with untyped-eval-unicity eval eval'
  ... | refl = refl
  untyped-eval-unicity EHole EHole = refl
  untyped-eval-unicity (EAsrt eval1 eval2 xc) (EAsrt eval1' eval2' xc')
    with untyped-eval-unicity eval1 eval1' | untyped-eval-unicity eval2 eval2'
  ... | refl | refl = refl
