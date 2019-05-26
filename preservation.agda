open import Nat
open import Prelude
open import List

open import contexts
open import core

open import lemmas-env

module preservation where
  preservation : ∀{Δ Σ' Γ E e r k τ} →
                   Δ , Σ' , Γ ⊢ E →
                   Δ , Σ' , Γ ⊢ e :: τ →
                   E ⊢ e ⇒ r ⊣ k →
                   Δ , Σ' ⊢ r ·: τ
  preservation ctxcons ta EFun = TALam ctxcons ta
  preservation ctxcons ta EFix = TAFix ctxcons ta
  preservation ctxcons (TAVar tah) (EVar h) with env-all-Γ ctxcons tah
  ... | π3 , π4 , π5 rewrite ctxunicity h π4 = π5
  preservation ctxcons (TAHole h) EHole = TAHole h ctxcons
  preservation ctxcons (TATpl h1 h2 h3) (ETuple h4 h5 h6) =
    TATpl (! h4 · h1) λ {i} i<∥rs∥ i<∥τs∥ →
      let i<∥es∥ = tr (λ y → i < y) (! h4) i<∥rs∥ in
      preservation ctxcons (h3 i<∥es∥ i<∥τs∥) (h6 i<∥es∥ i<∥rs∥ (tr (λ y → i < y) h5 i<∥es∥))
  preservation ctxcons (TACtor h1 h2 ta) (ECtor eval) = TACtor h1 h2 (preservation ctxcons ta eval)
  preservation ctxcons (TAApp _ ta-f ta-arg) (EApp CF∞ eval1 eval2 eval-ef) with preservation ctxcons ta-f eval1
  ... | TALam ctxcons-Ef (TALam x#Γ ta-ef) =
    preservation (EnvInd ctxcons-Ef (preservation ctxcons ta-arg eval2)) ta-ef eval-ef
  preservation ctxcons (TAApp _ ta-f ta-arg) (EAppFix CF∞ h eval1 eval2 eval-ef) rewrite h with preservation ctxcons ta-f eval1
  ... | TAFix ctxcons-Ef (TAFix f#Γ x#Γ ta-ef) =
    preservation (EnvInd (EnvInd ctxcons-Ef (preservation ctxcons ta-f eval1)) (preservation ctxcons ta-arg eval2)) ta-ef eval-ef
  preservation ctxcons (TAApp _ ta1 ta2) (EAppUnfinished eval1 _ _ eval2) =
    TAApp (preservation ctxcons ta1 eval1) (preservation ctxcons ta2 eval2)
  preservation ctxcons (TAGet _ i<∥τs∥ ta) (EGet h eval) with preservation ctxcons ta eval
  ... | TATpl _ h' = h' h i<∥τs∥
  preservation ctxcons (TAGet n==∥τs∥ i<∥τs∥ ta) (EGetUnfinished eval h) rewrite n==∥τs∥ = TAGet i<∥τs∥ (preservation ctxcons ta eval)
  preservation {Σ' = Σ'} ctxcons (TACase d∈Σ' ta h1 h2) (EMatch form eval-e eval-ec) with h2 form
  ... | _ , _ , _ , _ , c∈cctx2 , ta-ec with preservation ctxcons ta eval-e
  ... | TACtor {cctx = cctx} d∈Σ'2 c∈cctx ta' with ctxunicity {Γ = π1 Σ'} d∈Σ' d∈Σ'2
  ... | refl with ctxunicity {Γ = cctx} c∈cctx c∈cctx2
  ... | refl = preservation (EnvInd ctxcons ta') ta-ec eval-ec
  preservation ctxcons (TACase d∈Σ' ta h1 h2) (EMatchUnfinished eval h) =
    TACase d∈Σ' ctxcons (preservation ctxcons ta eval) h1 λ form' →
      let p1 , _ , _ , _ , p2 , p3 = h2 form' in
      p1 , _ , p2 , p3
  preservation ctxcons (TAAsrt _ ta1 ta2) (EAsrt eval1 eval2 _) = TATpl refl λ i<∥rs∥ → abort (n≮0 i<∥rs∥)
