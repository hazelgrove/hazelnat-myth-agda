open import Nat
open import Prelude
open import List

open import contexts
open import core

open import results-checks
open import preservation

module finality where
  finality : ∀{Δ Σ' Γ E e r k τ} →
               E env-final →
               Δ , Σ' , Γ ⊢ E →
               Δ , Σ' , Γ ⊢ e :: τ →
               E ⊢ e ⇒ r ⊣ k →
               r final
  finality E-final ctxcons (TAFix _) EFix = FFix E-final
  finality (EF E-fin) ctxcons (TAVar _) (EVar h) = E-fin h
  finality E-final ctxcons (TAApp _ ta-f ta-arg) (EAppFix {Ef = Ef} {f} {x} {ef} {r2 = r2} CF∞ h2 eval-f eval-arg eval-ef)
    rewrite h2 with preservation ctxcons ta-f eval-f
  ... | TAFix ctxcons-Ef (TAFix ta-ef) =
    finality (EF new-Ef+-final) new-ctxcons ta-ef eval-ef
    where
      new-ctxcons =
        EnvInd (EnvInd ctxcons-Ef (preservation ctxcons ta-f eval-f)) (preservation ctxcons ta-arg eval-arg)
      new-Ef-final  : ∀{x' rx'} → (x' , rx') ∈ (Ef ,, (f , [ Ef ]fix f ⦇·λ x => ef ·⦈)) → rx' final
      new-Ef-final  {x'} {rx'} h with ctx-split {Γ = Ef} h
      new-Ef-final  {x'} {rx'} h | Inl (_ , x'∈Ef) with finality E-final ctxcons ta-f eval-f
      ... | FFix (EF Ef-fin) = Ef-fin x'∈Ef
      new-Ef-final  {x'} {rx'} h | Inr (_ , rx'==r2) rewrite rx'==r2 = finality E-final ctxcons ta-f eval-f
      new-Ef+-final : ∀{x' rx'} → (x' , rx') ∈ (Ef ,, (f , [ Ef ]fix f ⦇·λ x => ef ·⦈) ,, (x , r2)) → rx' final
      new-Ef+-final {x'} {rx'} h with ctx-split {Γ = Ef ,, (f , [ Ef ]fix f ⦇·λ x => ef ·⦈)} h
      new-Ef+-final {x'} {rx'} h | Inl (_ , x'∈Ef+) = new-Ef-final x'∈Ef+
      new-Ef+-final {x'} {rx'} h | Inr (_ , rx'==r2) rewrite rx'==r2 = finality E-final ctxcons ta-arg eval-arg
  finality E-final ctxcons (TAApp h ta-f ta-arg) (EAppUnfinished eval-f h2 eval-arg) =
    FAp (finality E-final ctxcons ta-f eval-f) (finality E-final ctxcons ta-arg eval-arg) h2
  finality E-final ctxcons TAUnit EUnit = FUnit
  finality E-final ctxcons (TAPair _ ta1 ta2) (EPair eval1 eval2)
    = FPair (finality E-final ctxcons ta1 eval1) (finality E-final ctxcons ta2 eval2)
  finality E-final ctxcons (TAFst ta) (EFst eval)
    with finality E-final ctxcons ta eval
  ... | FPair fin _ = fin
  finality E-final ctxcons (TAFst ta) (EFstUnfinished eval ne)
    = FFst (finality E-final ctxcons ta eval) ne
  finality E-final ctxcons (TASnd ta) (ESnd eval)
    with finality E-final ctxcons ta eval
  ... | FPair _ fin = fin
  finality E-final ctxcons (TASnd ta) (ESndUnfinished eval ne)
    = FSnd (finality E-final ctxcons ta eval) ne
  finality E-final ctxcons (TACtor h h2 ta) (ECtor eval) = FCon (finality E-final ctxcons ta eval)
  finality {Σ' = Σ'} (EF E-fin) ctxcons (TACase d∈Σ'1 ta h1 h2) (EMatch {E = E} {xc = xc} {r' = r'} CF∞ form eval eval-ec)
    with h2 form
  ...  | _ , _ , _ , c∈cctx1 , ta-ec
    with preservation ctxcons ta eval
  ...  | TACtor {cctx = cctx} d∈Σ' c∈cctx ta-r'
    rewrite ctxunicity {Γ = π1 Σ'} d∈Σ'1 d∈Σ' | ctxunicity {Γ = cctx} c∈cctx1 c∈cctx =
      finality (EF new-E-final) (EnvInd ctxcons ta-r') ta-ec eval-ec
      where
        new-E-final : ∀{x' rx'} → (x' , rx') ∈ (E ,, (xc , r')) → rx' final
        new-E-final {x'} {rx'} x'∈E+ with ctx-split {Γ = E} x'∈E+
        ... | Inl (_ , x'∈E) = E-fin x'∈E
        ... | Inr (_ , rx'==r') rewrite rx'==r' with finality (EF E-fin) ctxcons ta eval
        ... | FCon r'-fin = r'-fin
  finality E-final ctxcons (TACase h ta h2 h3) (EMatchUnfinished eval h4) = FCase (finality E-final ctxcons ta eval) h4 E-final
  finality E-final ctxcons (TAHole _) EHole = FHole E-final
  finality E-final ctxcons (TAAsrt _ _ _) (EAsrt _ _ _) = FUnit
