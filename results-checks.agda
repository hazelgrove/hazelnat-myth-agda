open import Nat
open import Prelude
open import List

open import contexts
open import core

module results-checks where
  Coerce-preservation : ∀{Δ Σ' r v τ} →
                          Δ , Σ' ⊢ r ·: τ →
                          Coerce r := v →
                          Σ' ⊢ v ::ⱽ τ
  Coerce-preservation (TAFix x x₁) ()
  Coerce-preservation (TAApp ta-r ta-r₁) ()
  Coerce-preservation TAUnit CoerceUnit = TSVUnit
  Coerce-preservation (TAPair ta-r1 ta-r2) (CoercePair c-r1 c-r2)
    = TSVPair (Coerce-preservation ta-r1 c-r1) (Coerce-preservation ta-r2 c-r2)
  Coerce-preservation (TAFst ta-r) ()
  Coerce-preservation (TASnd ta-r) ()
  Coerce-preservation (TACtor h1 h2 ta-r) (CoerceCtor c-r)
    = TSVCtor h1 h2 (Coerce-preservation ta-r c-r)
  Coerce-preservation (TACase x x₁ ta-r x₂ x₃) ()
  Coerce-preservation (TAHole x x₁) ()

  {- TODO : We should revive this - it's a good sanity check.
            Of course, we have to decide what version of "complete" we want to use
            for results
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
