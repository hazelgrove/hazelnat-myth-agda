open import Nat
open import Prelude
open import List

open import contexts
open import core

open import preservation

module finality where
  finality : ∀{Δ Σ' Γ E e r k τ} →
               E env-final →
               Δ , Σ' , Γ ⊢ E →
               Δ , Σ' , Γ ⊢ e :: τ →
               E ⊢ e ⇒ r ⊣ k →
               r final
  finality E-final ctxcons (TALam _ _) EFun = FLam E-final
  finality E-final ctxcons (TAFix _ _ _) EFix = FFix E-final
  finality (EF E-fin) ctxcons (TAVar _) (EVar h) = E-fin h
  finality E-final ctxcons (TAApp _ ta-f ta-arg) (EApp {Ef = Ef} {x} {r2 = r2} eval-f eval-arg eval-ef)
    with preservation ctxcons ta-f eval-f
  ... | TALam ctxcons-Ef (TALam _ ta-ef) =
    finality (EF new-Ef-final) (EnvInd ctxcons-Ef (preservation ctxcons ta-arg eval-arg)) ta-ef eval-ef
    where
      new-Ef-final : ∀{x' rx'} → (x' , rx') ∈ (Ef ,, (x , r2)) → rx' final
      new-Ef-final {x'} {rx'} h with ctx-split {Γ = Ef} h
      new-Ef-final {x'} {rx'} h | Inl x'∈Ef with finality E-final ctxcons ta-f eval-f
      ... | FLam (EF Ef-fin) = Ef-fin x'∈Ef
      new-Ef-final {x'} {rx'} h | Inr (x'#Ef , _ , rx'==r2) rewrite rx'==r2 = finality E-final ctxcons ta-arg eval-arg
  finality E-final ctxcons (TAApp _ ta-f ta-arg) (EAppFix {Ef = Ef} {f} {x} {ef} {r2 = r2} h2 eval-f eval-arg eval-ef)
    rewrite h2 with preservation ctxcons ta-f eval-f
  ... | TAFix ctxcons-Ef (TAFix _ _ ta-ef) =
    finality (EF new-Ef+-final) new-ctxcons ta-ef eval-ef
    where
      new-ctxcons =
        EnvInd (EnvInd ctxcons-Ef (preservation ctxcons ta-f eval-f)) (preservation ctxcons ta-arg eval-arg)
      new-Ef-final  : ∀{x' rx'} → (x' , rx') ∈ (Ef ,, (f , [ Ef ]fix f ⦇·λ x => ef ·⦈)) → rx' final
      new-Ef-final  {x'} {rx'} h with ctx-split {Γ = Ef} h
      new-Ef-final  {x'} {rx'} h | Inl x'∈Ef with finality E-final ctxcons ta-f eval-f
      ... | FFix (EF Ef-fin) = Ef-fin x'∈Ef
      new-Ef-final  {x'} {rx'} h | Inr (x'#Ef , _ , rx'==r2) rewrite rx'==r2 = finality E-final ctxcons ta-f eval-f
      new-Ef+-final : ∀{x' rx'} → (x' , rx') ∈ (Ef ,, (f , [ Ef ]fix f ⦇·λ x => ef ·⦈) ,, (x , r2)) → rx' final
      new-Ef+-final {x'} {rx'} h with ctx-split {Γ = Ef ,, (f , [ Ef ]fix f ⦇·λ x => ef ·⦈)} h
      new-Ef+-final {x'} {rx'} h | Inl x'∈Ef+ = new-Ef-final x'∈Ef+
      new-Ef+-final {x'} {rx'} h | Inr (x'#Ef+ , _ , rx'==r2) rewrite rx'==r2 = finality E-final ctxcons ta-arg eval-arg
  finality E-final ctxcons (TAApp h ta-f ta-arg) (EAppUnfinished eval-f h2 h3 eval-arg) =
    FAp (finality E-final ctxcons ta-f eval-f) (finality E-final ctxcons ta-arg eval-arg) h2 h3
  finality E-final ctxcons (TATpl h h2 h3) (ETuple h4 h5 h6) =
    FTpl λ {i} i<∥rs∥ →
      let
        tr< = λ {x y} eq st → tr {x = x} {y} (λ y → i < y) eq st
        i<∥es∥ = tr< (! h4) i<∥rs∥
        i<∥ks∥ = tr< h5 i<∥es∥
        i<∥τs∥ = tr< h i<∥es∥
      in
      finality E-final ctxcons (h3 i<∥es∥ i<∥τs∥) (h6 i<∥es∥ i<∥rs∥ i<∥ks∥)
  finality E-final ctxcons (TAGet ∥rs⊫=∥τs∥ i<∥τs∥ ta) (EGet h eval)
    with finality E-final ctxcons ta eval
  ... | FTpl all-fin = all-fin h
  finality E-final ctxcons (TAGet h i<∥τs∥ ta) (EGetUnfinished eval h2) = FGet (finality E-final ctxcons ta eval) h2
  finality E-final ctxcons (TACtor h h2 ta) (ECtor eval) = FCon (finality E-final ctxcons ta eval)
  finality {Σ' = Σ'} (EF E-fin) ctxcons (TACase d∈Σ'1 ta h1 h2) (EMatch {E = E} {xj = xj} {r' = r'} i<∥rules∥ form eval eval-ej)
    with h2 i<∥rules∥ form
  ...  | _ , _ , _ , _ , _ , Cj∈cctx1 , ta-ej
    with preservation ctxcons ta eval
  ...  | TACtor {cctx = cctx} d∈Σ' Cj∈cctx ta-r'
    rewrite ctxunicity {Γ = π1 Σ'} d∈Σ'1 d∈Σ' | ctxunicity {Γ = cctx} Cj∈cctx1 Cj∈cctx =
      finality (EF new-E-final) (EnvInd ctxcons ta-r') ta-ej eval-ej
      where
        new-E-final : ∀{x' rx'} → (x' , rx') ∈ (E ,, (xj , r')) → rx' final
        new-E-final {x'} {rx'} x'∈E+ with ctx-split {Γ = E} x'∈E+
        ... | Inl x'∈E = E-fin x'∈E
        ... | Inr (x'#E , _ , rx'==r') rewrite rx'==r' with finality (EF E-fin) ctxcons ta eval
        ... | FCon r'-fin = r'-fin
  finality E-final ctxcons (TACase h ta h2 h3) (EMatchUnfinished eval h4) = FCase (finality E-final ctxcons ta eval) h4 E-final
  finality E-final ctxcons (TAHole _) EHole = FHole E-final
  finality E-final ctxcons (TAPF _) ()
  finality E-final ctxcons (TAAsrt _ _ _) (EAsrt _ _ _) = FTpl (λ i<∥rs∥ → abort (n≮0 i<∥rs∥))
