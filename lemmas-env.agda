open import Prelude
open import Nat
open import core
open import contexts

module lemmas-env where
  env-ctx-same-1 : ∀{Δ Σ' Γ E x} →
                     Δ , Σ' , Γ ⊢ E →
                     x # E →
                     x # Γ
  env-ctx-same-1 EnvId h = x#∅
  env-ctx-same-1 {x = x} (EnvInd {E = E} {x = x'} ctxcons _) x#E+
    with natEQ x x'
  ... | Inl refl = abort (x#E+ (_ , x,a∈Γ,,x,a {Γ = E}))
  ... | Inr x≠x'
    with env-ctx-same-1 ctxcons (x#Γ+→x#Γ {Γ = E} x#E+)
  ... | x#Γ = x#Γ→x#Γ+ x≠x' x#Γ

  env-ctx-same-2 : ∀{Δ Σ' Γ E x} →
                     Δ , Σ' , Γ ⊢ E →
                     x # Γ →
                     x # E
  env-ctx-same-2 EnvId h = x#∅
  env-ctx-same-2 {x = x} (EnvInd {Γ = Γ} {x = x'} ctxcons _) x#Γ+
    with natEQ x x'
  ... | Inl refl = abort (x#Γ+ (_ , x,a∈Γ,,x,a {Γ = Γ}))
  ... | Inr x≠x'
    with env-ctx-same-2 ctxcons (x#Γ+→x#Γ {Γ = Γ} x#Γ+)
  ... | x#E = x#Γ→x#Γ+ x≠x' x#E

  env-all-Γ : ∀{Δ Σ' Γ E x τ} →
                Δ , Σ' , Γ ⊢ E →
                (x , τ) ∈ Γ →
                Σ[ r ∈ result ] ((x , r) ∈ E ∧ Δ , Σ' ⊢ r ·: τ)
  env-all-Γ EnvId x∈Γ = abort (x#∅ (_ , x∈Γ))
  env-all-Γ {x = x} (EnvInd {Γ = Γ} {E} {x'} ctxcons ta) x∈Γ
    with natEQ x x'
  ... | Inl refl
          rewrite ctxunicity x∈Γ (x,a∈Γ,,x,a {Γ = Γ})
            = _ , x,a∈Γ,,x,a {Γ = E} , ta
  ... | Inr x≠x'
    with env-all-Γ ctxcons (x∈Γ+→x∈Γ {Γ = Γ} x≠x' x∈Γ)
  ... | _ , x∈E , ta-rec = _ , x∈Γ→x∈Γ+ x≠x' x∈E , ta-rec

  env-all-E : ∀{Δ Σ' Γ E x r} →
                Δ , Σ' , Γ ⊢ E →
                (x , r) ∈ E →
                Σ[ τ ∈ typ ] ((x , τ) ∈ Γ ∧ Δ , Σ' ⊢ r ·: τ)
  env-all-E EnvId x∈E = abort (x#∅ (_ , x∈E))
  env-all-E {x = x} (EnvInd {Γ = Γ} {E} {x'} ctxcons ta) x∈E
    with natEQ x x'
  ... | Inl refl
          rewrite ctxunicity x∈E (x,a∈Γ,,x,a {Γ = E})
            = _ , x,a∈Γ,,x,a {Γ = Γ} , ta
  ... | Inr x≠x'
    with env-all-E ctxcons (x∈Γ+→x∈Γ {Γ = E} x≠x' x∈E)
  ... | _ , x∈Γ , ta-rec = _ , x∈Γ→x∈Γ+ x≠x' x∈Γ , ta-rec
