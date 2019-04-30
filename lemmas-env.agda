open import Prelude
open import Nat
open import core
open import contexts

module lemmas-env where
  env-ctx-same-1 : ∀{Δ Σ' Γ E x} →
                     Δ , Σ' , Γ ⊢ E →
                     x # E →
                     x # Γ
  env-ctx-same-1 EnvId h = refl
  env-ctx-same-1 {x = x} (EnvInd {Γ = Γ} {E} {x'} ctxcons x₂) x#E with lem-union-none {Γ = E} x#E
  env-ctx-same-1 {x = x} (EnvInd {Γ = Γ} {E} {x'} ctxcons x₂) x#E | π3 , π4 = lem-apart-union1 Γ _ _ (env-ctx-same-1 ctxcons π4) (lem-neq-apart (flip π3))

  env-ctx-same-2 : ∀{Δ Σ' Γ E x} →
                     Δ , Σ' , Γ ⊢ E →
                     x # Γ →
                     x # E
  env-ctx-same-2 EnvId h = refl
  env-ctx-same-2 {x = x} (EnvInd {Γ = Γ} {E} {x'} ctxcons x₂) x#Γ with lem-union-none {Γ = Γ} x#Γ
  env-ctx-same-2 {x = x} (EnvInd {Γ = Γ} {E} {x'} ctxcons x₂) x#Γ | π3 , π4 = lem-apart-union1 E _ _ (env-ctx-same-2 ctxcons π4) (lem-neq-apart (flip π3))

  env-all-Γ : ∀{Δ Σ' Γ E x τ} →
                Δ , Σ' , Γ ⊢ E →
                (x , τ) ∈ Γ →
                Σ[ r ∈ result ] ((x , r) ∈ E ∧ Δ , Σ' ⊢ r ·: τ)
  env-all-Γ EnvId ()
  env-all-Γ {x = x} (EnvInd {Γ = Γ} {E} {x'} {τx} ctxcons ta) x∈Γ with ctxindirect Γ x
  env-all-Γ {x = x} (EnvInd {Γ = Γ} {E} {x'} {τx} ctxcons ta) x∈Γ | Inl (π3 , π4) with env-all-Γ ctxcons π4
  env-all-Γ {x = x} (EnvInd {Γ = Γ} {E} {x'} {τx} ctxcons ta) x∈Γ | Inl (π3 , π4) | π5 , π6 , π7 rewrite π4 | someinj x∈Γ = _ , x∈∪l E _ _ _ π6 , π7
  env-all-Γ {x = x} (EnvInd {Γ = Γ} {E} {x'} {τx} ctxcons ta) x∈Γ | Inr x#Γ with natEQ x x' | lem-dom-union-apt1 {Δ1 = Γ} x#Γ x∈Γ
  env-all-Γ {x = x} (EnvInd {Γ = Γ} {E} {.x} {τx} ctxcons ta) x∈Γ | Inr x#Γ | Inl refl | τx=τ rewrite x∈■ x τx | someinj τx=τ = _ , ctx-top E _ _ (env-ctx-same-2 ctxcons x#Γ) , ta
  env-all-Γ {x = x} (EnvInd {Γ = Γ} {E} {x'} {τx} ctxcons ta) x∈Γ | Inr x#Γ | Inr ne   | h = abort (somenotnone (! (lem-neq-union-eq ne h)))

  env-all-E : ∀{Δ Σ' Γ E x r} →
                Δ , Σ' , Γ ⊢ E →
                (x , r) ∈ E →
                Σ[ τ ∈ typ ] ((x , τ) ∈ Γ ∧ Δ , Σ' ⊢ r ·: τ)
  env-all-E EnvId ()
  env-all-E {x = x} (EnvInd {Γ = Γ} {E} {x'} {rx = rx} ctxcons ta) x∈E with ctxindirect E x
  env-all-E {x = x} (EnvInd {Γ = Γ} {E} {x'} {rx = rx} ctxcons ta) x∈E | Inl (π3 , π4) with env-all-E ctxcons π4
  env-all-E {x = x} (EnvInd {Γ = Γ} {E} {x'} {rx = rx} ctxcons ta) x∈E | Inl (π3 , π4) | π5 , π6 , π7 rewrite π4 | someinj x∈E = _ , x∈∪l Γ _ _ _ π6 , π7
  env-all-E {x = x} (EnvInd {Γ = Γ} {E} {x'} {rx = rx} ctxcons ta) x∈E | Inr x#E with natEQ x x' | lem-dom-union-apt1 {Δ1 = E} x#E x∈E
  env-all-E {x = x} (EnvInd {Γ = Γ} {E} {.x} {rx = rx} ctxcons ta) x∈E | Inr x#E | Inl refl | rx=r rewrite x∈■ x rx | someinj rx=r = _ , ctx-top Γ _ _ (env-ctx-same-1 ctxcons x#E) , ta
  env-all-E {x = x} (EnvInd {Γ = Γ} {E} {x'} {rx = rx} ctxcons ta) x∈E | Inr x#E | Inr ne   | h    = abort (somenotnone (! (lem-neq-union-eq ne h)))
