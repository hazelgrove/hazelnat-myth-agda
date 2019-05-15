open import Nat
open import Prelude
open import List

open import contexts
open import core

open import preservation
open import lemmas-complete
open import results-checks

module completeness where
  -- if an example type-checks, it's complete
  ex-ta-complete : ∀{Σ' ex τ} → Σ' ⊢ ex :· τ → ex ex-complete
  ex-ta-complete (TATpl ∥exs⊫=∥τs∥ h) = EXCTpl (λ {i} i<∥exs∥ → ex-ta-complete (h i<∥exs∥ (tr (λ y → i < y) ∥exs⊫=∥τs∥ i<∥exs∥)))
  ex-ta-complete (TACtor _ _ ta) = EXCCtor (ex-ta-complete ta)
  ex-ta-complete {ex = PF pf} (TAPF h) =
    EXCPF (PFC λ i<∥pf∥ →
               λ where refl →
                         let (rval , rta , exta) = h i<∥pf∥ refl in
                         values-complete rval , ex-ta-complete exta)

  -- any hole is new to a complete expression
  e-complete-hnn : ∀{e u} → e ecomplete → hole-name-new e u
  e-complete-hnn (ECLam cmp) = HNNLam (e-complete-hnn cmp)
  e-complete-hnn (ECFix cmp) = HNNFix (e-complete-hnn cmp)
  e-complete-hnn ECVar = HNNVar
  e-complete-hnn (ECAp cmp1 cmp2) = HNNAp (e-complete-hnn cmp1) (e-complete-hnn cmp2)
  e-complete-hnn (ECTpl h) = HNNTup λ i<∥es∥ → e-complete-hnn (h i<∥es∥)
  e-complete-hnn (ECGet cmp) = HNNGet (e-complete-hnn cmp)
  e-complete-hnn (ECCtor cmp) = HNNCtor (e-complete-hnn cmp)
  e-complete-hnn (ECCase cmp h) = HNNCase (e-complete-hnn cmp) λ i<∥rules∥ → e-complete-hnn (h i<∥rules∥)
  e-complete-hnn (ECPF cmp) = HNNPF cmp
  e-complete-hnn (ECAsrt cmp1 cmp2) = HNNAsrt (e-complete-hnn cmp1) (e-complete-hnn cmp2)

  {- TODO : probably delete
  e-hnn-complete : ∀{e} → (∀{u} → hole-name-new e u) → e ecomplete
  e-hnn-complete hnn∀ = {!!}
  -}

  -- a complete expression is holes-disjoint to all expressions
  e-complete-disjoint : ∀{e1 e2} → e1 ecomplete → holes-disjoint e1 e2
  e-complete-disjoint (ECLam cmp) = HDLam (e-complete-disjoint cmp)
  e-complete-disjoint (ECFix cmp) = HDFix (e-complete-disjoint cmp)
  e-complete-disjoint ECVar = HDVar
  e-complete-disjoint (ECAp cmp1 cmp2) = HDAp (e-complete-disjoint cmp1) (e-complete-disjoint cmp2)
  e-complete-disjoint (ECTpl h) = HDTup λ i<∥es∥ → e-complete-disjoint (h i<∥es∥)
  e-complete-disjoint (ECGet cmp) = HDGet (e-complete-disjoint cmp)
  e-complete-disjoint (ECCtor cmp) = HDCtor (e-complete-disjoint cmp)
  e-complete-disjoint (ECCase cmp h) = HDCase (e-complete-disjoint cmp) λ i<∥rules∥ → e-complete-disjoint (h i<∥rules∥)
  e-complete-disjoint (ECPF cmp) = HDPF cmp
  e-complete-disjoint (ECAsrt cmp1 cmp2) = HDAsrt (e-complete-disjoint cmp1) (e-complete-disjoint cmp2)

  -- TODO a holes-disjoint-sym check - very involved but arguably pretty important

  -- if e evals to r, and e is complete, then r is complete
  eval-completeness : ∀{Δ Σ' Γ E e r τ k} →
                        E env-complete →
                        Δ , Σ' , Γ ⊢ E →
                        Δ , Σ' , Γ ⊢ e :: τ →
                        E ⊢ e ⇒ r ⊣ k →
                        e ecomplete →
                        r rcomplete
  eval-completeness Ecmp Γ⊢E (TALam _ _) EFun (ECLam ecmp) = RCLam Ecmp ecmp
  eval-completeness Ecmp Γ⊢E (TAFix _ _ _) EFix (ECFix ecmp) = RCFix Ecmp ecmp
  eval-completeness (ENVC Ecmp) Γ⊢E (TAVar _) (EVar h) ECVar = Ecmp h
  eval-completeness Ecmp Γ⊢E (TAApp _ ta-f ta-arg) (EApp {Ef = Ef} {x} {r2 = r2} eval-f eval-arg eval-ef) (ECAp cmp-f cmp-arg)
    with eval-completeness Ecmp Γ⊢E ta-f eval-f cmp-f | preservation Γ⊢E ta-f eval-f
  ... | RCLam (ENVC Efcmp) efcmp | TALam Γ'⊢Ef (TALam _ ta-ef)
    = eval-completeness (ENVC env-cmp) (EnvInd Γ'⊢Ef (preservation Γ⊢E ta-arg eval-arg)) ta-ef eval-ef efcmp
      where
        env-cmp : ∀{x' rx'} → (x' , rx') ∈ (Ef ,, (x , r2)) → rx' rcomplete
        env-cmp {x'} {rx'} h with ctx-split {Γ = Ef} h
        env-cmp {x'} {rx'} h | Inl x'∈Ef = Efcmp x'∈Ef
        env-cmp {x'} {rx'} h | Inr (x'#Ef , _ , rx'==r2) rewrite rx'==r2 =
          eval-completeness Ecmp Γ⊢E ta-arg eval-arg cmp-arg
  eval-completeness Ecmp Γ⊢E (TAApp _ ta-f ta-arg) (EAppFix {Ef = Ef} {f} {x} {ef} {r2 = r2} h eval-f eval-arg eval-ef) (ECAp cmp-f cmp-arg)
    rewrite h with eval-completeness Ecmp Γ⊢E ta-f eval-f cmp-f | preservation Γ⊢E ta-f eval-f
  ... | RCFix (ENVC Efcmp) efcmp | TAFix Γ'⊢Ef (TAFix _ _ ta-ef) =
    eval-completeness (ENVC new-Ef+-cmp) new-ctxcons ta-ef eval-ef efcmp
    where
      new-ctxcons =
        EnvInd (EnvInd Γ'⊢Ef (preservation Γ⊢E ta-f eval-f)) (preservation Γ⊢E ta-arg eval-arg)
      new-Ef-cmp  : ∀{x' rx'} → (x' , rx') ∈ (Ef ,, (f , [ Ef ]fix f ⦇·λ x => ef ·⦈)) → rx' rcomplete
      new-Ef-cmp  {x'} {rx'} h with ctx-split {Γ = Ef} h
      new-Ef-cmp  {x'} {rx'} h | Inl x'∈Ef = Efcmp x'∈Ef
      new-Ef-cmp  {x'} {rx'} h | Inr (x'#Ef , _ , rx'==r2) rewrite rx'==r2 = RCFix (ENVC Efcmp) efcmp
      new-Ef+-cmp : ∀{x' rx'} → (x' , rx') ∈ (Ef ,, (f , [ Ef ]fix f ⦇·λ x => ef ·⦈) ,, (x , r2)) → rx' rcomplete
      new-Ef+-cmp {x'} {rx'} h with ctx-split {Γ = Ef ,, (f , [ Ef ]fix f ⦇·λ x => ef ·⦈)} h
      new-Ef+-cmp {x'} {rx'} h | Inl x'∈Ef+ = new-Ef-cmp x'∈Ef+
      new-Ef+-cmp {x'} {rx'} h | Inr (x'#Ef+ , _ , rx'==r2) rewrite rx'==r2 =
        eval-completeness Ecmp Γ⊢E ta-arg eval-arg cmp-arg
  eval-completeness Ecmp Γ⊢E (TAApp _ ta1 ta2) (EAppUnfinished eval1 _ _ eval2) (ECAp ecmp1 ecmp2) =
    RCAp (eval-completeness Ecmp Γ⊢E ta1 eval1 ecmp1) (eval-completeness Ecmp Γ⊢E ta2 eval2 ecmp2)
  eval-completeness Ecmp Γ⊢E (TATpl ∥es⊫=∥τs∥ _ tas) (ETuple ∥es⊫=∥rs∥ ∥es⊫=∥ks∥ evals) (ECTpl cmps) =
    RCTpl λ {i} i<∥rs∥ →
      let
        tr< = λ {x y} eq st → tr {x = x} {y} (λ y → i < y) eq st
        i<∥es∥ = tr< (! ∥es⊫=∥rs∥) i<∥rs∥
        i<∥ks∥ = tr< ∥es⊫=∥ks∥ i<∥es∥
        i<∥τs∥ = tr< ∥es⊫=∥τs∥ i<∥es∥
      in
      eval-completeness Ecmp Γ⊢E (tas i<∥es∥ i<∥τs∥) (evals i<∥es∥ i<∥rs∥ i<∥ks∥) (cmps i<∥es∥)
  eval-completeness Ecmp Γ⊢E (TAGet ∥rs⊫=∥τs∥ i<∥τs∥ ta) (EGet i<∥rs∥ eval) (ECGet ecmp)
    with eval-completeness Ecmp Γ⊢E ta eval ecmp
  ... | RCTpl h = h i<∥rs∥
  eval-completeness Ecmp Γ⊢E (TAGet _ i<∥τs∥ ta) (EGetUnfinished eval _) (ECGet ecmp) =
    RCGet (eval-completeness Ecmp Γ⊢E ta eval ecmp)
  eval-completeness Ecmp Γ⊢E (TACtor _ _ ta) (ECtor eval) (ECCtor ecmp) =
    RCCtor (eval-completeness Ecmp Γ⊢E ta eval ecmp)
  eval-completeness {Σ' = Σ'} (ENVC Ecmp) Γ⊢E (TACase d∈Σ'1 ta h1 h2) (EMatch {E = E} {xj = xj} {r' = r'} j<∥rules∥ form eval eval-ej) (ECCase ecmp rules-cmp)
    with h2 j<∥rules∥ form
  ... | _ , _ , _ , _ , _ , Cj∈cctx1 , ta-ej
    with preservation Γ⊢E ta eval
  ... | TACtor {cctx = cctx} d∈Σ' Cj∈cctx ta-r'
    rewrite ctxunicity {Γ = π1 Σ'} d∈Σ'1 d∈Σ' | ctxunicity {Γ = cctx} Cj∈cctx1 Cj∈cctx with rules-cmp j<∥rules∥
  ... | ejcmp rewrite ! form =
    eval-completeness (ENVC new-E-cmp) (EnvInd Γ⊢E ta-r') ta-ej eval-ej ejcmp
    where
      new-E-cmp : ∀{x' rx'} → (x' , rx') ∈ (E ,, (xj , r')) → rx' rcomplete
      new-E-cmp {x'} {rx'} x'∈E+ with ctx-split {Γ = E} x'∈E+
      ... | Inl x'∈E = Ecmp x'∈E
      ... | Inr (x'#E , _ , rx'==r') rewrite rx'==r'
        with eval-completeness (ENVC Ecmp) Γ⊢E ta eval ecmp
      ... | RCCtor r'cmp = r'cmp
  eval-completeness Ecmp Γ⊢E (TACase _ ta _ _) (EMatchUnfinished eval _) (ECCase ecmp rulescmp) =
    RCCase Ecmp (eval-completeness Ecmp Γ⊢E ta eval ecmp) rulescmp
  eval-completeness Ecmp Γ⊢E (TAHole _) EHole ()
  eval-completeness Ecmp Γ⊢E (TAPF _) () ecmp
  eval-completeness Ecmp Γ⊢E (TAAsrt _ _ _) (EAsrt _ _ _) (ECAsrt _ _) =
    RCTpl (λ i<∥rs∥ → abort (n≮0 i<∥rs∥))
