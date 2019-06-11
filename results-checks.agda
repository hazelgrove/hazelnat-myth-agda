open import Nat
open import Prelude
open import List

open import contexts
open import core

module results-checks where
  -- all values are complete and final
  mutual
    values-complete : ∀{r} → r value → r rcomplete
    values-complete (VLam E-vals e-complete) = RCLam (env-values-complete E-vals) e-complete
    values-complete (VFix E-vals e-complete) = RCFix (env-values-complete E-vals) e-complete
    values-complete (VTpl h) = RCTpl λ i<∥rs∥ → values-complete (h i<∥rs∥)
    values-complete (VCon val) = RCCtor (values-complete val)
    values-complete (VPF h) = RCPF (pf-value-complete h)

    values-final : ∀{r} → r value → r final
    values-final (VLam h _) = FLam (env-values-final h)
    values-final (VFix h _) = FFix (env-values-final h)
    values-final (VTpl h) = FTpl λ i<∥rs∥ → values-final (h i<∥rs∥)
    values-final (VCon val) = FCon (values-final val)
    values-final (VPF h) = FPF (pf-value-final h)

    env-values-complete : ∀{E} → E env-values → E env-complete
    env-values-complete (EF E-vals) = ENVC λ rx∈E → values-complete (E-vals rx∈E)

    env-values-final : ∀{E} → E env-values → E env-final
    env-values-final (EF E-vals) = EF λ rx∈E → values-final (E-vals rx∈E)

    pf-value-complete : ∀{pf} → pf pf-value → pf pf-complete
    pf-value-complete (PFV pf-vals) =
      PFC λ i<∥pf∥ → (
            let (val-cmp , ex-cmp) = pf-vals i<∥pf∥ in
            values-complete val-cmp , ex-values-complete ex-cmp)

    pf-value-final : ∀{pf} → pf pf-value → pf pf-final
    pf-value-final (PFV pf-vals) =
      PFF λ i<∥pf∥ → (
            let (val-fin , ex-fin) = pf-vals i<∥pf∥ in
            values-final val-fin , ex-values-final ex-fin)

    ex-values-complete : ∀{ex} → ex ex-value → ex ex-complete
    ex-values-complete (EXVPF pf-val) = EXCPF (pf-value-complete pf-val)
    ex-values-complete (EXVTpl h) = EXCTpl λ i<∥exs∥ → ex-values-complete (h i<∥exs∥)
    ex-values-complete (EXVCtor ex-val) = EXCCtor (ex-values-complete ex-val)

    ex-values-final : ∀{ex} → ex ex-value → ex ex-final
    ex-values-final (EXVPF pf-val) = EXFPF (pf-value-final pf-val)
    ex-values-final (EXVTpl h) = EXFTpl λ i<∥exs∥ → ex-values-final (h i<∥exs∥)
    ex-values-final (EXVCtor ex-val) = EXFCtor (ex-values-final ex-val)

    -- if an example type-checks, it's a value
    ex-ta-value : ∀{Σ' ex τ} → Σ' ⊢ ex :· τ → ex ex-value
    ex-ta-value (TATpl ∥exs∥==∥τs∥ h)
      = EXVTpl (λ {i ex-i} exs[i]==ex-i →
          let _ , τs[i]==τ-i = ∥l1∥==∥l2∥→l1[i]→l2[i] ∥exs∥==∥τs∥ exs[i]==ex-i in
          ex-ta-value (h exs[i]==ex-i τs[i]==τ-i))
    ex-ta-value (TACtor _ _ ta) = EXVCtor (ex-ta-value ta)
    ex-ta-value {ex = PF pf} (TAPF h)
      = EXVPF (PFV λ {i v-i ex-i} pf[i]==v,ex →
          let (rval , rta , exta) = h pf[i]==v,ex in
          rval , (ex-ta-value exta))

    -- pf-ta-value : ∀{Σ' pf τ} → Σ' ⊢ ex :· τ → ex ex-value

  {- TODO : not currently true because pf ∘ blah is complete and final but not a value
  -- all complete finals (that type-check) are values
  mutual
    complete-finals-values : ∀{Δ Σ' r τ} →
                               Δ , Σ' ⊢ r ·: τ →
                               r rcomplete →
                               r final →
                               r value
    complete-finals-values (TALam Γ⊢E _) (RCLam E-cmp e-cmp) (FLam E-fin) =
      VLam (env-complete-final-values Γ⊢E E-cmp E-fin) e-cmp
    complete-finals-values (TAFix Γ⊢E _) (RCFix E-cmp e-cmp) (FFix E-fin) =
      VFix (env-complete-final-values Γ⊢E E-cmp E-fin) e-cmp
    complete-finals-values (TAApp ta1 ta2) (RCAp cmp1 cmp2) (FAp fin1 fin2 h1 h2)
      with complete-finals-values ta1 cmp1 fin1
    complete-finals-values (TAApp ta1 ta2) (RCAp cmp1 cmp2) (FAp fin1 fin2 h1 h2) | VLam _ _ = abort (h1 refl)
    complete-finals-values (TAApp ta1 ta2) (RCAp cmp1 cmp2) (FAp fin1 fin2 h1 h2) | VFix _ _ = abort (h2 refl)
    complete-finals-values (TAApp () ta2) (RCAp cmp1 cmp2) (FAp fin1 fin2 h1 h2)  | VTpl _
    complete-finals-values (TAApp () ta2) (RCAp cmp1 cmp2) (FAp fin1 fin2 h1 h2)  | VCon _
    complete-finals-values (TAApp ta1 ta2) (RCAp cmp1 cmp2) (FAp fin1 fin2 h1 h2) | VPF _ = {!!}
    complete-finals-values (TATpl ∥rs⊫=∥τs∥ ta) (RCTpl h1) (FTpl h2) =
      VTpl λ {i} i<∥rs∥ → complete-finals-values (ta i<∥rs∥ (tr (λ y → i < y) ∥rs⊫=∥τs∥ i<∥rs∥)) (h1 i<∥rs∥) (h2 i<∥rs∥)
    complete-finals-values (TAGet i<∥τs∥ ta) (RCGet cmp) (FGet fin x) = {!!}
    complete-finals-values (TACtor _ _ ta) (RCCtor cmp) (FCon fin) =
      VCon (complete-finals-values ta cmp fin)
    complete-finals-values (TACase x x₁ ta x₂ x₃) (RCCase x₄ cmp x₅) (FCase fin x₆ x₇) = {!!}
    complete-finals-values (TAHole _ _) () fin
    complete-finals-values (TAPF x) (RCPF x₁) (FPF x₂) = {!!}

    env-complete-final-values : ∀{Δ Σ' Γ E} →
                                  Δ , Σ' , Γ ⊢ E →
                                  E env-complete →
                                  E env-final →
                                  E env-values
    env-complete-final-values ta (ENVC E-cmp) (EF E-fin) =
      EF (λ rx∈E → complete-finals-values (π2 (π2 (env-all-E ta rx∈E))) (E-cmp rx∈E) (E-fin rx∈E))
  -}
