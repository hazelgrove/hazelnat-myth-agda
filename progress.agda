open import Nat
open import Prelude
open import List

open import contexts
open import core

open import lemmas-env
open import lemmas-progress
open import constraints-checks

-- TODO we're forced to prove this weaker version, since the strong version is
--      unprovable. That said, this weak version is still disappointing, so we
--      should come up with some more thoerems to shore up its deficiencies -
--      in particular, we should do something to mitigate the fact that an e
--      may succeed for every even n and fail for every odd n
--      - also, that evaluation may return different results for different n
-- TODO complete, then delete
--      e => r → ∀{n} e [n]=> r
--        something similar for =>∅ ?
--      (Σ[r] (e => r) ∧ e => ∅) → ⊥
--      ∀{k} → Σ[r] (e [k]=> r) ∨ e [k]=> ∅
module progress where
  progress : ∀{Δ Σ' Γ E e τ n} →
               Δ , Σ' , Γ ⊢ E →
               Δ , Σ' , Γ ⊢ e :: τ →
               -- Either there's some properly-typed result that e will eval to ...
               Σ[ r ∈ result ] Σ[ k ∈ constraints ] (
                  (E ⊢ e ⌊ ⛽⟨ n ⟩ ⌋⇒ r ⊣ k) ∧
                  Δ , Σ' ⊢ r ·: τ)
               -- ... or evaluation will have a constraint failure
               ∨ E ⊢ e ⌊ ⛽⟨ n ⟩ ⌋⇒∅

  lemma-progress-tpl : ∀{Δ Σ' Γ E es τs n} →
               Δ , Σ' , Γ ⊢ E →
               Δ , Σ' , Γ ⊢ ⟨ es ⟩ :: ⟨ τs ⟩ →
               Σ[ rs ∈ List result ] Σ[ k ∈ constraints ] (
                  (E ⊢ ⟨ es ⟩ ⌊ ⛽⟨ n ⟩ ⌋⇒ ⟨ rs ⟩ ⊣ k) ∧
                  Δ , Σ' ⊢ ⟨ rs ⟩ ·: ⟨ τs ⟩)
               ∨ E ⊢ ⟨ es ⟩ ⌊ ⛽⟨ n ⟩ ⌋⇒∅

  progress {n = Z} Γ⊢E ta
    = Inl (_ , _ , ELimit , π2 (typ-inhabitance-pres Γ⊢E ta))
  progress {n = 1+ n} Γ⊢E ta'@(TALam _ ta)   = Inl (_ , _ , EFun , TALam Γ⊢E ta')
  progress {n = 1+ n} Γ⊢E ta'@(TAFix _ _ ta) = Inl (_ , _ , EFix , TAFix Γ⊢E ta')
  progress {n = 1+ n} Γ⊢E (TAVar x∈Γ)
    with env-all-Γ Γ⊢E x∈Γ
  ... | _ , x∈E , ta = Inl (_ , _ , EVar x∈E , ta)
  progress {n = 1+ n} Γ⊢E (TAApp _ ta-f ta-arg)
    with progress Γ⊢E ta-arg
  ... | Inr arg-fails = Inr (EFAppArg arg-fails)
  ... | Inl (rarg , _ , arg-evals , ta-rarg)
    with progress Γ⊢E ta-f
  ... | Inr f-fails = Inr (EFAppFun f-fails)
  progress {n = 1+ n} Γ⊢E (TAApp _ ta-f ta-arg) | Inl (rarg , _ , arg-evals , ta-rarg) | Inl (([ E' ]λ x => ef) , _ , f-evals , TALam Γ'⊢E' (TALam _ ta-ef))
    with progress {n = n} (EnvInd Γ'⊢E' ta-rarg) ta-ef
  ... | Inr ef-fails = Inr (EFAppEval CF⛽ f-evals arg-evals ef-fails)
  ... | Inl (ref , _ , ef-evals , ta-ref) = Inl (_ , _ , EApp CF⛽ f-evals arg-evals ef-evals , ta-ref)
  progress {n = 1+ n} Γ⊢E (TAApp _ ta-f ta-arg) | Inl (rarg , _ , arg-evals , ta-rarg) | Inl ([ E' ]fix f ⦇·λ x => ef ·⦈ , _ , f-evals , ta'@(TAFix Γ'⊢E' (TAFix _ _ ta-ef)))
    with progress {n = n} (EnvInd (EnvInd Γ'⊢E' ta') ta-rarg) ta-ef
  ... | Inr ef-fails = Inr (EFAppFixEval CF⛽ refl f-evals arg-evals ef-fails)
  ... | Inl (ref , _ , ef-evals , ta-ref) = Inl (_ , _ , EAppFix CF⛽ refl f-evals arg-evals ef-evals , ta-ref)
  progress {n = 1+ n} Γ⊢E (TAApp _ ta-f ta-arg) | Inl (rarg , _ , arg-evals , ta-rarg) | Inl ([ E' ]??[ u ] , _ , f-evals , ta-rf)
    = Inl (_ , _ , EAppUnfinished f-evals (λ ()) (λ ()) arg-evals , TAApp ta-rf ta-rarg)
  progress {n = 1+ n} Γ⊢E (TAApp _ ta-f ta-arg) | Inl (rarg , _ , arg-evals , ta-rarg) | Inl ((rf-f ∘ rf-arg) , _ , f-evals , ta-rf)
    = Inl (_ , _ , EAppUnfinished f-evals (λ ()) (λ ()) arg-evals , TAApp ta-rf ta-rarg)
  progress {n = 1+ n} Γ⊢E (TAApp _ ta-f ta-arg) | Inl (rarg , _ , arg-evals , ta-rarg) | Inl ((get[ i' th-of n' ] rf) , _ , f-evals , ta-rf)
    = Inl (_ , _ , EAppUnfinished f-evals (λ ()) (λ ()) arg-evals , TAApp ta-rf ta-rarg)
  progress {n = 1+ n} Γ⊢E (TAApp _ ta-f ta-arg) | Inl (rarg , _ , arg-evals , ta-rarg) | Inl ([ E' ]case rf of⦃· rules ·⦄ , _ , f-evals , ta-rf)
    = Inl (_ , _ , EAppUnfinished f-evals (λ ()) (λ ()) arg-evals , TAApp ta-rf ta-rarg)
  progress {n = 1+ n} Γ⊢E (TAApp _ ta-f ta-arg) | Inl (rarg , _ , arg-evals , ta-rarg) | Inl (PF pf , _ , f-evals , ta-rf)
    = Inl (_ , _ , EAppUnfinished f-evals (λ ()) (λ ()) arg-evals , TAApp ta-rf ta-rarg)
  progress {n = 1+ n} Γ⊢E ta@(TATpl ∥es∥==∥τs∥ _ tas)
    with lemma-progress-tpl {n = 1+ n} Γ⊢E ta
  ... | Inr tpl-fails                    = Inr tpl-fails
  ... | Inl (_ , _ , tpl-evals , ta-tpl) = Inl (_ , _ , tpl-evals , ta-tpl)
  progress {Δ} {Σ'} {E = E} {τ = τ} {1+ n} Γ⊢E (TAGet {i = i} {len} {e} len==∥τs∥ τs[i] ta)
    with progress Γ⊢E ta
  ... | Inr e-fails = Inr (EFGet e-fails)
  ... | Inl (⟨ rs ⟩ , _ , e-evals , TATpl ∥rs∥==∥τs∥ tas)
          rewrite len==∥τs∥
            = let _ , rs[i] = ∥l1∥==∥l2∥→l1[i]→l2[i] (! ∥rs∥==∥τs∥) τs[i] in
              Inl (_ , _ , EGet (! ∥rs∥==∥τs∥) rs[i] e-evals , tas rs[i] τs[i])
  ... | Inl (([ x ]λ x₁ => x₂) , _ , e-evals , TALam _ ())
  ... | Inl ([ x ]fix x₁ ⦇·λ x₂ => x₃ ·⦈ , _ , e-evals , TAFix _ ())
  ... | Inl ([ x ]??[ x₁ ] , _ , e-evals , r-ta)
          rewrite len==∥τs∥ = Inl (_ , _ , EGetUnfinished e-evals (λ ()) , TAGet τs[i] r-ta)
  ... | Inl ((r ∘ r₁) , _ , e-evals , r-ta)
          rewrite len==∥τs∥ = Inl (_ , _ , EGetUnfinished e-evals (λ ()) , TAGet τs[i] r-ta)
  ... | Inl ((get[ x th-of x₁ ] r) , _ , e-evals , r-ta)
          rewrite len==∥τs∥ = Inl (_ , _ , EGetUnfinished e-evals (λ ()) , TAGet τs[i] r-ta)
  ... | Inl ([ x ]case r of⦃· x₁ ·⦄ , _ , e-evals , r-ta)
          rewrite len==∥τs∥ = Inl (_ , _ , EGetUnfinished e-evals (λ ()) , TAGet τs[i] r-ta)
  ... | Inl (PF _ , _ , e-evals , TAPF ())
  progress {n = 1+ n} Γ⊢E (TACtor d∈Σ' c∈d ta)
    with progress Γ⊢E ta
  ... | Inr e-fails = Inr (EFCtor e-fails)
  ... | Inl (_ , _ , e-evals , ta-r) = Inl (_ , _ , ECtor e-evals , TACtor d∈Σ' c∈d ta-r)
  progress {Σ' = Σ'} {n = 1+ n} Γ⊢E (TACase d∈σ' e-ta cctx⊆rules h-rules)
    with progress Γ⊢E e-ta
  ... | Inr e-fails = Inr (EFMatchScrut e-fails)
  ... | Inl (([ x ]λ x₁ => x₂) , _ , e-evals , TALam _ ())
  ... | Inl ([ x ]fix x₁ ⦇·λ x₂ => x₃ ·⦈ , _ , e-evals , TAFix _ ())
  ... | Inl ([ x ]??[ x₁ ] , _ , e-evals , ta-re)
          = Inl (_ , _ , EMatchUnfinished e-evals (λ ()) , TACase d∈σ' Γ⊢E ta-re cctx⊆rules (λ form →
                 let xc#Γ , _ , _ , _ , c∈cctx , ec-ta = h-rules form in
                 xc#Γ , _ , c∈cctx , ec-ta))
  ... | Inl ((re ∘ re₁) , _ , e-evals , ta-re)
          = Inl (_ , _ , EMatchUnfinished e-evals (λ ()) , TACase d∈σ' Γ⊢E ta-re cctx⊆rules (λ form →
                 let xc#Γ , _ , _ , _ , c∈cctx , ec-ta = h-rules form in
                 xc#Γ , _ , c∈cctx , ec-ta))
  ... | Inl ((get[ x th-of x₁ ] re) , _ , e-evals , ta-re)
          = Inl (_ , _ , EMatchUnfinished e-evals (λ ()) , TACase d∈σ' Γ⊢E ta-re cctx⊆rules (λ form →
                 let xc#Γ , _ , _ , _ , c∈cctx , ec-ta = h-rules form in
                 xc#Γ , _ , c∈cctx , ec-ta))
  ... | Inl ([ x ]case re of⦃· x₁ ·⦄ , _ , e-evals , ta-re)
          = Inl (_ , _ , EMatchUnfinished e-evals (λ ()) , TACase d∈σ' Γ⊢E ta-re cctx⊆rules (λ form →
                 let xc#Γ , _ , _ , _ , c∈cctx , ec-ta = h-rules form in
                 xc#Γ , _ , c∈cctx , ec-ta))
  ... | Inl (PF x , _ , e-evals , TAPF ())
  ... | Inl ((C[ c ] re) , _ , e-evals , TACtor d∈'σ' c∈cctx' ta-re)
    rewrite ctxunicity d∈'σ' d∈σ'
    with π2 (cctx⊆rules (_ , c∈cctx'))
  ... | form
    with h-rules form
  ... | _ , _ , _ , _ , c∈cctx , ec-ta
    rewrite ctxunicity c∈cctx c∈cctx'
    with progress {n = n} (EnvInd Γ⊢E ta-re) ec-ta
  ... | Inr ec-fails = Inr (EFMatchRule CF⛽ form e-evals ec-fails)
  ... | Inl (_ , _ , ec-evals , ta-rec) = Inl (_ , _ , EMatch CF⛽ form e-evals ec-evals , ta-rec)
  progress {n = 1+ n} Γ⊢E (TAHole u∈Δ) = Inl (_ , _ , EHole , TAHole u∈Δ Γ⊢E)
  progress {n = 1+ n} Γ⊢E (TAPF ta) = Inl (_ , _ , EPF , TAPF ta)
  progress {n = 1+ n} Γ⊢E (TAAsrt _ ta1 ta2)
    with progress Γ⊢E ta1
  ... | Inr e1-fails = Inr (EFAsrtL e1-fails)
  ... | Inl (r1 , _ , e1-evals , ta-r1)
    with progress Γ⊢E ta2
  ... | Inr e2-fails = Inr (EFAsrtR e2-fails)
  ... | Inl (r2 , _ , e2-evals , ta-r2)
    with constraints-dec r1 r2
  ... | Inl (_ , c-succ) = Inl (_ , _ , EAsrt e1-evals e2-evals c-succ , TATpl refl (λ ()))
  ... | Inr c-fail       = Inr (EFAsrt e1-evals e2-evals c-fail)

  lemma-progress-tpl {es = []} {[]} Γ⊢E ta
    = Inl (_ , _ , ETuple refl refl (λ ()) , TATpl refl (λ ()))
  lemma-progress-tpl {es = []} {_ :: τs} Γ⊢E (TATpl () _ _)
  lemma-progress-tpl {es = _ :: es} {[]} Γ⊢E (TATpl () _ _)
  lemma-progress-tpl {Δ} {Σ'} {Γ} {E} {es = e :: es} {τ :: τs} {0} Γ⊢E ta'
    with typ-inhabitance-pres-tpl Γ⊢E ta'
  ... | _ , ta = Inl (_ , _ , ELimit , ta)
  lemma-progress-tpl {Δ} {Σ'} {Γ} {E} {es = e :: es} {τ :: τs} {1+ n} Γ⊢E (TATpl ∥es∥==∥τs∥ hh h)
    with progress {e = e} {n = 1+ n} Γ⊢E (h {Z} refl refl)
  ... | Inr h-fails = Inr (EFTpl {j = Z} refl h-fails)
  ... | Inl (r , k , h-evals , ta-h)
    with lemma-progress-tpl {n = 1+ n} Γ⊢E (TATpl
           (1+inj ∥es∥==∥τs∥)
           (λ i≠j es[i] es[j] → hh (1+inj-cp i≠j) es[i] es[j])
           λ {i} es[i] τs[i] → h {1+ i} es[i] τs[i])
  ... | Inr (EFTpl {j = j} j<∥es∥ fails') = Inr (EFTpl {j = 1+ j} j<∥es∥ fails')
  ... | Inl (rs , _ , ETuple {ks = ks} ∥es∥==∥rs∥ ∥es∥==∥ks∥ evals , TATpl ∥rs∥==∥τs∥ h2)
          = Inl (r :: rs , _ , ETuple (1+ap ∥es∥==∥rs∥) (1+ap ∥es∥==∥ks∥) (λ {i} → f-evals {i}) , TATpl (1+ap ∥rs∥==∥τs∥) (λ {i} → f-ta {i}))
            where
              f-evals : ∀{i e-i r-i k-i} →
                          (e :: es) ⟦ i ⟧ == Some e-i →
                          (r :: rs) ⟦ i ⟧ == Some r-i →
                          (k :: ks) ⟦ i ⟧ == Some k-i →
                          E ⊢ e-i ⌊ ⛽⟨ 1+ n ⟩ ⌋⇒ r-i ⊣ k-i
              f-evals {Z}    e::es[i] r::rs[i] k::ks[i]
                rewrite someinj e::es[i] | someinj r::rs[i] | someinj k::ks[i]
                  = h-evals
              f-evals {1+ i} e::es[i] r::rs[i] k::ks[i] = evals e::es[i] r::rs[i] k::ks[i]
              f-ta : ∀{i r-i τ-i} →
                       (r :: rs) ⟦ i ⟧ == Some r-i →
                       (τ :: τs) ⟦ i ⟧ == Some τ-i →
                       Δ , Σ' ⊢ r-i ·: τ-i
              f-ta {Z}    r::rs[i] τ::τs[i]
                rewrite someinj r::rs[i] | someinj τ::τs[i]
                  = ta-h
              f-ta {1+ i} r::rs[i] τ::τs[i] = h2 r::rs[i] τ::τs[i]

{- TODO delete - this strong version is unprovable
module progress where
  progress : ∀{Δ Σ' Γ E e τ} →
               Δ , Σ' , Γ ⊢ E →
               Δ , Σ' , Γ ⊢ e :: τ →
               -- Either there's some properly-typed result that e will eval to
               -- for any beta reduction limit ...
               Σ[ r ∈ result ] (
                  Δ , Σ' ⊢ r ·: τ ∧
                  ∀{n} → Σ[ k ∈ constraints ] (E ⊢ e ⌊ ⛽⟨ n ⟩ ⌋⇒ r ⊣ k))
               ∨
               -- ... or evaluation will have a constraint failure for any
               -- beta reduction limit
               (∀{n} → E ⊢ e ⌊ ⛽⟨ n ⟩ ⌋⇒∅)
  progress Γ⊢E ta'@(TALam _ ta) = Inl (_ , TALam Γ⊢E ta' , (_ , EFun))
  progress Γ⊢E ta'@(TAFix _ _ ta) = Inl (_ , TAFix Γ⊢E ta' , (_ , EFix))
  progress Γ⊢E (TAVar x∈Γ)
    with env-all-Γ Γ⊢E x∈Γ
  ... | _ , x∈E , ta = Inl (_ , ta , (_ , EVar x∈E))
  progress Γ⊢E (TAApp _ ta-f ta-arg)
    with progress Γ⊢E ta-arg
  ... | Inr arg-fails = Inr (EFAppArg arg-fails)
  ... | Inl (_ , ta-rarg , arg-evals)
    with progress Γ⊢E ta-f
  ... | Inr f-fails = Inr (EFAppFun f-fails)
  progress Γ⊢E (TAApp _ ta-f ta-arg) | Inl (_ , ta-rarg , arg-evals) | Inl (([ E' ]λ x => ef) , TALam Γ'⊢E' (TALam x#Γ' ta-ef) , f-evals)
    with progress (EnvInd Γ'⊢E' ta-rarg) ta-ef
  ... | q = {!!}
  progress Γ⊢E (TAApp _ ta-f ta-arg) | Inl (_ , ta-rarg , arg-evals) | Inl ([ E' ]fix f ⦇·λ x => ef ·⦈ , ta-rf , f-evals) = {!!}
  progress Γ⊢E (TAApp _ ta-f ta-arg) | Inl (_ , ta-rarg , arg-evals) | Inl ([ x ]??[ x₁ ] , ta-rf , f-evals) = {!!}
  progress Γ⊢E (TAApp _ ta-f ta-arg) | Inl (_ , ta-rarg , arg-evals) | Inl ((rf ∘ rf₁) , ta-rf , f-evals) = {!!}
  progress Γ⊢E (TAApp _ ta-f ta-arg) | Inl (_ , ta-rarg , arg-evals) | Inl ((get[ x th-of x₁ ] rf) , ta-rf , f-evals) = {!!}
  progress Γ⊢E (TAApp _ ta-f ta-arg) | Inl (_ , ta-rarg , arg-evals) | Inl ([ x ]case rf of⦃· x₁ ·⦄ , ta-rf , f-evals) = {!!}
  progress Γ⊢E (TAApp _ ta-f ta-arg) | Inl (_ , ta-rarg , arg-evals) | Inl (PF x , ta-rf , f-evals) = {!!}
  progress Γ⊢E (TATpl ∥es∥==∥τs∥ _ tas) = {!!}
  progress {Δ} {Σ'} {E = E} {τ = τ} Γ⊢E (TAGet {i = i} {len} {e} len==∥τs∥ i<∥τs∥ ta)
    with progress Γ⊢E ta
  ... | Inr e-fails = Inr (EFGet e-fails)
  ... | Inl (⟨ rs ⟩ , TATpl ∥rs∥==∥τs∥ tas , e-evals)
          = let i<∥rs∥ = tr (λ y → i < y) (! ∥rs∥==∥τs∥) i<∥τs∥ in
            Inl (_ , tas i<∥rs∥ i<∥τs∥ , _ , EGet (len==∥τs∥ · ! ∥rs∥==∥τs∥) i<∥rs∥ (π2 e-evals))
  ... | Inl (([ x ]λ x₁ => x₂) , TALam _ () , e-evals)
  ... | Inl ([ x ]fix x₁ ⦇·λ x₂ => x₃ ·⦈ , TAFix _ () , e-evals)
  ... | Inl ([ x ]??[ x₁ ] , ta-r , e-evals)
          rewrite len==∥τs∥ = Inl (_ , TAGet i<∥τs∥ ta-r , _ , EGetUnfinished (π2 e-evals) λ ())
  ... | Inl ((r ∘ r₁) , ta-r , e-evals)
          rewrite len==∥τs∥ = Inl (_ , TAGet i<∥τs∥ ta-r , _ , EGetUnfinished (π2 e-evals) λ ())
  ... | Inl ((get[ x th-of x₁ ] r) , ta-r , e-evals)
          rewrite len==∥τs∥ = Inl (_ , TAGet i<∥τs∥ ta-r , _ , EGetUnfinished (π2 e-evals) λ ())
  ... | Inl ([ x ]case r of⦃· x₁ ·⦄ , ta-r , e-evals)
          rewrite len==∥τs∥ = Inl (_ , TAGet i<∥τs∥ ta-r , _ , EGetUnfinished (π2 e-evals) λ ())
  ... | Inl (PF x , TAPF () , e-evals)
  progress Γ⊢E (TACtor d∈Σ' c∈d ta)
    with progress Γ⊢E ta
  ... | Inl (_ , ta-r , e-evals) = Inl (_ , TACtor d∈Σ' c∈d ta-r , _ , ECtor (π2 e-evals))
  ... | Inr e-fails = Inr (EFCtor e-fails)
  progress Γ⊢E (TACase x ta x₁ x₂) = {!!}
  progress Γ⊢E (TAHole u∈Δ) = Inl (_ , TAHole u∈Δ Γ⊢E , (_ , EHole))
  progress Γ⊢E (TAPF ta) = Inl (_ , TAPF ta , (_ , EPF))
  progress Γ⊢E (TAAsrt x ta ta₁) = {!!}
-}
