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

  typ-inhabitance-pres-tpl : ∀{Δ Σ' Γ E es τs} →
                               Δ , Σ' , Γ ⊢ E →
                               Δ , Σ' , Γ ⊢ ⟨ es ⟩ :: ⟨ τs ⟩ →
                               Σ[ rs ∈ List result ] (Δ , Σ' ⊢ ⟨ rs ⟩ ·: ⟨ τs ⟩)

  typ-inhabitance-pres Γ⊢E ta@(TALam _ e-ta)   = _ , (TALam Γ⊢E ta)
  typ-inhabitance-pres Γ⊢E ta@(TAFix _ _ e-ta) = _ , (TAFix Γ⊢E ta)
  typ-inhabitance-pres Γ⊢E (TAVar x∈Γ)
    with env-all-Γ Γ⊢E x∈Γ
  ... | _ , x∈E , r-ta = _ , r-ta
  typ-inhabitance-pres Γ⊢E (TAApp _ f-ta arg-ta)
    with typ-inhabitance-pres Γ⊢E f-ta | typ-inhabitance-pres Γ⊢E arg-ta
  ... | _ , rf-ta | _ , rarg-ta = _ , TAApp rf-ta rarg-ta
  typ-inhabitance-pres Γ⊢E ta@(TATpl {es = es} ∥es∥==∥τs∥ _ tas)
    with typ-inhabitance-pres-tpl Γ⊢E ta
  ... | _ , rslt = _ , rslt
  typ-inhabitance-pres Γ⊢E (TAGet n==∥τs∥ i<∥τs∥ e-ta)
    with typ-inhabitance-pres Γ⊢E e-ta
  ... | _ , r-ta = _ , TAGet i<∥τs∥ r-ta
  typ-inhabitance-pres Γ⊢E (TACtor d∈Σ' c∈d e-ta)
    with typ-inhabitance-pres Γ⊢E e-ta
  ... | _ , r-ta = _ , TACtor d∈Σ' c∈d r-ta
  typ-inhabitance-pres Γ⊢E (TACase d∈Σ' e-ta h1 h2)
    with typ-inhabitance-pres Γ⊢E e-ta
  ... | _ , r-ta = _ , TACase d∈Σ' Γ⊢E r-ta h1 λ form →
                       let h4 , _ , _ , _ , h5 , h6 = h2 form in
                       h4 , _ , h5 , h6
  typ-inhabitance-pres Γ⊢E (TAHole u∈Δ) = _ , TAHole u∈Δ Γ⊢E
  typ-inhabitance-pres Γ⊢E (TAPF ta) = _ , TAPF ta
  typ-inhabitance-pres Γ⊢E (TAAsrt _ e-ta1 e-ta2)
    = _ , TATpl refl (λ i<∥rs∥ i<∥τs∥ → abort (n≮0 i<∥τs∥))

  typ-inhabitance-pres-tpl {es = []} {[]} Γ⊢E es-ta
    = _ , TATpl refl (λ i<∥rs∥ i<∥τs∥ → abort (n≮0 i<∥τs∥))
  typ-inhabitance-pres-tpl {es = []} {_ :: τs} Γ⊢E (TATpl () x₂ x₃)
  typ-inhabitance-pres-tpl {es = _ :: es} {[]} Γ⊢E (TATpl () x₂ x₃)
  typ-inhabitance-pres-tpl {Δ} {Σ'} {Γ} {E} {e :: es} {τ :: τs} Γ⊢E (TATpl ∥es∥==∥τs∥ hh h)
    with typ-inhabitance-pres-tpl Γ⊢E (TATpl (1+inj ∥es∥==∥τs∥) hh' h') | typ-inhabitance-pres {e = e} Γ⊢E (h 0<1+n 0<1+n)
         where
           hh' : {i j : Nat} (i<∥es∥ : i < ∥ es ∥) (j<∥es∥ : j < ∥ es ∥) → i ≠ j → holes-disjoint (es ⟦ i given i<∥es∥ ⟧) (es ⟦ j given j<∥es∥ ⟧)
           hh' i<∥es∥ j<∥es∥ i≠j
             rewrite index-proof-irrelevance {p1 = i<∥es∥} {1+n<1+m→n<m (n<m→1+n<1+m i<∥es∥)}
                   | index-proof-irrelevance {p1 = j<∥es∥} {1+n<1+m→n<m (n<m→1+n<1+m j<∥es∥)}
               = hh (n<m→1+n<1+m i<∥es∥) (n<m→1+n<1+m j<∥es∥) (1+inj-cp i≠j)
           h' : {i : Nat} (i<∥es∥ : i < ∥ es ∥) (i<∥τs∥ : i < ∥ τs ∥) → Δ , Σ' , Γ ⊢ es ⟦ i given i<∥es∥ ⟧ :: (τs ⟦ i given i<∥τs∥ ⟧)
           h' i<∥es∥ i<∥τs∥
             rewrite index-proof-irrelevance {p1 = i<∥es∥} {1+n<1+m→n<m (n<m→1+n<1+m i<∥es∥)}
                   | index-proof-irrelevance {p1 = i<∥τs∥} {1+n<1+m→n<m (n<m→1+n<1+m i<∥τs∥)}
               = h (n<m→1+n<1+m i<∥es∥) (n<m→1+n<1+m i<∥τs∥)
  ... | rs , TATpl ∥rs∥==∥τs∥ h2 | r , r-ta
          = r :: rs , TATpl (1+ap ∥rs∥==∥τs∥) λ {
              {Z}    i<∥rs∥ i<∥τs∥ → r-ta ;
              {1+ i} i<∥rs∥ i<∥τs∥ → h2 (1+n<1+m→n<m i<∥rs∥) (1+n<1+m→n<m i<∥τs∥)
            }
