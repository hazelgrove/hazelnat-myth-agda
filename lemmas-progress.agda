open import Nat
open import Prelude
open import List

open import contexts
open import core

open import lemmas-env

module lemmas-progress where
  typ-inhabitance-pres : ∀{Δ Σ' Γ E e τ} →
                           Δ , Σ' , Γ ⊢ E →
                           Δ , Σ' , Γ ⊢ e :: τ →
                           Σ[ r ∈ result ] (Δ , Σ' ⊢ r ·: τ)

  typ-inhabitance-pres Γ⊢E ta@(TAFix e-ta) = _ , (TAFix Γ⊢E ta)
  typ-inhabitance-pres Γ⊢E (TAVar x∈Γ)
    with env-all-Γ Γ⊢E x∈Γ
  ... | _ , x∈E , r-ta = _ , r-ta
  typ-inhabitance-pres Γ⊢E (TAApp _ f-ta arg-ta)
    with typ-inhabitance-pres Γ⊢E f-ta | typ-inhabitance-pres Γ⊢E arg-ta
  ... | _ , rf-ta | _ , rarg-ta = _ , TAApp rf-ta rarg-ta
  typ-inhabitance-pres Γ⊢E TAUnit = _ , TAUnit
  typ-inhabitance-pres Γ⊢E (TAPair _ ta1 ta2)
    with typ-inhabitance-pres Γ⊢E ta1 | typ-inhabitance-pres Γ⊢E ta2
  ... | _ , r-ta1 | _ , r-ta2 = _ , TAPair r-ta1 r-ta2
  typ-inhabitance-pres Γ⊢E (TAFst ta)
    with typ-inhabitance-pres Γ⊢E ta
  ... | _ , r-ta = _ , TAFst r-ta
  typ-inhabitance-pres Γ⊢E (TASnd ta)
    with typ-inhabitance-pres Γ⊢E ta
  ... | _ , r-ta = _ , TASnd r-ta
  typ-inhabitance-pres Γ⊢E (TACtor d∈Σ' c∈d e-ta)
    with typ-inhabitance-pres Γ⊢E e-ta
  ... | _ , r-ta = _ , TACtor d∈Σ' c∈d r-ta
  typ-inhabitance-pres Γ⊢E (TACase d∈Σ' e-ta h1 h2)
    with typ-inhabitance-pres Γ⊢E e-ta
  ... | _ , r-ta = _ , TACase d∈Σ' Γ⊢E r-ta h1 λ form →
                       let _ , _ , _ , h5 , h6 = h2 form in
                       _ , h5 , h6
  typ-inhabitance-pres Γ⊢E (TAHole u∈Δ) = _ , TAHole u∈Δ Γ⊢E
  typ-inhabitance-pres Γ⊢E (TAAsrt _ e-ta1 e-ta2) = _ , TAUnit
