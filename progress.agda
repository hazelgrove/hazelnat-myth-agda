open import Nat
open import Prelude
open import List

open import contexts
open import core

open import lemmas-env
open import lemmas-progress
open import decidability
open import results-checks

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

  xc-progress : ∀{Δ Σ' r1 r2 τ n} →
                  Δ , Σ' ⊢ r1 ·: τ →
                  Δ , Σ' ⊢ r2 ·: τ →
                  Σ[ k ∈ constraints ] Constraints⦃ r1 , r2 ⦄⌊ ⛽⟨ n ⟩ ⌋:= k
                  ∨ Constraints⦃ r1 , r2 ⦄⌊ ⛽⟨ n ⟩ ⌋:=∅

  xb-progress : ∀{Δ Σ' r ex τ n} →
                  Δ , Σ' ⊢ r ·: τ →
                  Δ , Σ' ⊢ ex :· τ →
                  Σ[ k ∈ constraints ] (r ⇐ ex ⌊ ⛽⟨ n ⟩ ⌋:= k)
                  ∨ r ⇐ ex ⌊ ⛽⟨ n ⟩ ⌋:=∅

  rule-fails : {n↓ : Nat} {E : env} {r : result} {ex : ex} → Set
  rule-fails {n↓} {E} {r} {ex} =
              Σ[ c-j ∈ Nat ] Σ[ x-j ∈ Nat ] Σ[ e-j ∈ exp ] (
                 r ⇐ C[ c-j ] ¿¿ ⌊ ⛽⟨ 1+ n↓ ⟩ ⌋:=∅
                 ∨ Σ[ k1 ∈ constraints ] (
                      r ⇐ C[ c-j ] ¿¿ ⌊ ⛽⟨ 1+ n↓ ⟩ ⌋:= k1 ∧ (E ,, (x-j , C⁻[ c-j ] r)) ⊢ e-j ⌊ ⛽⟨ n↓ ⟩ ⌋⇒∅)
                 ∨ Σ[ k1 ∈ constraints ] Σ[ k2 ∈ constraints ] Σ[ r-j ∈ result ] (
                      r ⇐ C[ c-j ] ¿¿ ⌊ ⛽⟨ 1+ n↓ ⟩ ⌋:= k1 ∧ (E ,, (x-j , C⁻[ c-j ] r)) ⊢ e-j ⌊ ⛽⟨ n↓ ⟩ ⌋⇒ r-j ⊣ k2 ∧ r-j ⇐ ex ⌊ ⛽⟨ n↓ ⟩ ⌋:=∅))

  lemma-xb-progress-case : ∀{Δ Σ' E r rules ex τ n n↓} →
                             (n == 1+ n↓) →
                             (len : Nat) →
                             (unchecked : rule ctx) →
                             len == ∥ unchecked ∥ →
                             (failed : (rule-fails {n↓} {E} {r} {ex}) ctx) →
                             (∀{c rule} → (c , rule) ∈ unchecked → (c , rule) ∈ rules) →
                             (∀{c c-j x-j e-j p-j} →
                                (c , c-j , x-j , e-j , p-j) ∈ failed →
                                c == c-j ∧ (c , |C x-j => e-j) ∈ rules) →
                             (∀{c} → dom rules c → dom unchecked c ∨ dom failed c) →
                             Δ , Σ' ⊢ [ E ]case r of⦃· rules ·⦄ ·: τ →
                             Δ , Σ' ⊢ ex :· τ →
                             ex ≠ ¿¿ →
                             Σ[ k ∈ constraints ] ([ E ]case r of⦃· rules ·⦄ ⇐ ex ⌊ ⛽⟨ n ⟩ ⌋:= k)
                             ∨ [ E ]case r of⦃· rules ·⦄ ⇐ ex ⌊ ⛽⟨ n ⟩ ⌋:=∅

  progress {n = Z} Γ⊢E ta
    = Inl (_ , _ , ELimit , π2 (typ-inhabitance-pres Γ⊢E ta))
  progress {n = 1+ n} Γ⊢E ta'@(TAFix ta) = Inl (_ , _ , EFix , TAFix Γ⊢E ta')
  progress {n = 1+ n} Γ⊢E (TAVar x∈Γ)
    with env-all-Γ Γ⊢E x∈Γ
  ... | _ , x∈E , ta = Inl (_ , _ , EVar x∈E , ta)
  progress {n = 1+ n} Γ⊢E (TAApp _ ta-f ta-arg)
    with progress Γ⊢E ta-arg
  ... | Inr arg-fails = Inr (EFAppArg arg-fails)
  ... | Inl (rarg , _ , arg-evals , ta-rarg)
    with progress Γ⊢E ta-f
  ... | Inr f-fails = Inr (EFAppFun f-fails)
  progress {n = 1+ n} Γ⊢E (TAApp _ ta-f ta-arg) | Inl (rarg , _ , arg-evals , ta-rarg) | Inl ([ E' ]fix f ⦇·λ x => ef ·⦈ , _ , f-evals , ta'@(TAFix Γ'⊢E' (TAFix ta-ef)))
    with progress {n = n} (EnvInd (EnvInd Γ'⊢E' ta') ta-rarg) ta-ef
  ... | Inr ef-fails = Inr (EFAppFixEval CF⛽ refl f-evals arg-evals ef-fails)
  ... | Inl (ref , _ , ef-evals , ta-ref) = Inl (_ , _ , EAppFix CF⛽ refl f-evals arg-evals ef-evals , ta-ref)
  progress {n = 1+ n} Γ⊢E (TAApp _ ta-f ta-arg) | Inl (rarg , _ , arg-evals , ta-rarg) | Inl ([ E' ]??[ u ] , _ , f-evals , ta-rf)
    = Inl (_ , _ , EAppUnfinished f-evals (λ ()) arg-evals , TAApp ta-rf ta-rarg)
  progress {n = 1+ n} Γ⊢E (TAApp _ ta-f ta-arg) | Inl (rarg , _ , arg-evals , ta-rarg) | Inl ((rf-f ∘ rf-arg) , _ , f-evals , ta-rf)
    = Inl (_ , _ , EAppUnfinished f-evals (λ ()) arg-evals , TAApp ta-rf ta-rarg)
  progress {n = 1+ n} Γ⊢E (TAApp _ ta-f ta-arg) | Inl (rarg , _ , arg-evals , ta-rarg) | Inl (fst _ , _ , f-evals , ta-rf)
    = Inl (_ , _ , EAppUnfinished f-evals (λ ()) arg-evals , TAApp ta-rf ta-rarg)
  progress {n = 1+ n} Γ⊢E (TAApp _ ta-f ta-arg) | Inl (rarg , _ , arg-evals , ta-rarg) | Inl (snd _ , _ , f-evals , ta-rf)
    = Inl (_ , _ , EAppUnfinished f-evals (λ ()) arg-evals , TAApp ta-rf ta-rarg)
  progress {n = 1+ n} Γ⊢E (TAApp _ ta-f ta-arg) | Inl (rarg , _ , arg-evals , ta-rarg) | Inl ([ E' ]case rf of⦃· rules ·⦄ , _ , f-evals , ta-rf)
    = Inl (_ , _ , EAppUnfinished f-evals (λ ()) arg-evals , TAApp ta-rf ta-rarg)
  progress {n = 1+ n} Γ⊢E (TAApp _ ta-f ta-arg) | Inl (rarg , _ , arg-evals , ta-rarg) | Inl ((C⁻[ _ ] _) , _ , f-evals , ta-rf)
    = Inl (_ , _ , EAppUnfinished f-evals (λ ()) arg-evals , TAApp ta-rf ta-rarg)
  progress {n = 1+ n} Γ⊢E TAUnit = Inl (_ , _ , EUnit , TAUnit)
  progress {n = 1+ n} Γ⊢E (TAPair _ ta1 ta2)
    with progress Γ⊢E ta1
  ... | Inr fails                    = Inr (EFPair1 fails)
  ... | Inl (_ , _ , evals1 , ta-r1)
    with progress Γ⊢E ta2
  ... | Inr fails                    = Inr (EFPair2 fails)
  ... | Inl (_ , _ , evals2 , ta-r2) = Inl (_ , _ , EPair evals1 evals2 , TAPair ta-r1 ta-r2)
  progress {Δ} {Σ'} {E = E} {τ = τ} {1+ n} Γ⊢E (TAFst ta)
    with progress Γ⊢E ta
  ... | Inr fails = Inr (EFFst fails)
  progress {Δ} {Σ'} {E = E} {τ = τ} {1+ n} Γ⊢E (TAFst ta) | Inl (⟨ r1 , r2 ⟩ , _ , evals , TAPair ta-r1 ta-r2)
    = Inl (_ , _ , EFst evals , ta-r1)
  progress {Δ} {Σ'} {E = E} {τ = τ} {1+ n} Γ⊢E (TAFst ta) | Inl ([ x ]fix x₁ ⦇·λ x₂ => x₃ ·⦈ , _ , evals , TAFix _ ())
  progress {Δ} {Σ'} {E = E} {τ = τ} {1+ n} Γ⊢E (TAFst ta) | Inl ((C⁻[ x ] q) , _ , evals , ta-r)
    = Inl (_ , _ , EFstUnfinished evals (λ ()) , TAFst ta-r)
  progress {Δ} {Σ'} {E = E} {τ = τ} {1+ n} Γ⊢E (TAFst ta) | Inl ([ x ]??[ x₁ ] , _ , evals , ta-r)
    = Inl (_ , _ , EFstUnfinished evals (λ ()) , TAFst ta-r)
  progress {Δ} {Σ'} {E = E} {τ = τ} {1+ n} Γ⊢E (TAFst ta) | Inl ((q ∘ q₁) , _ , evals , ta-r)
    = Inl (_ , _ , EFstUnfinished evals (λ ()) , TAFst ta-r)
  progress {Δ} {Σ'} {E = E} {τ = τ} {1+ n} Γ⊢E (TAFst ta) | Inl (fst q , _ , evals , ta-r)
    = Inl (_ , _ , EFstUnfinished evals (λ ()) , TAFst ta-r)
  progress {Δ} {Σ'} {E = E} {τ = τ} {1+ n} Γ⊢E (TAFst ta) | Inl (snd q , _ , evals , ta-r)
    = Inl (_ , _ , EFstUnfinished evals (λ ()) , TAFst ta-r)
  progress {Δ} {Σ'} {E = E} {τ = τ} {1+ n} Γ⊢E (TAFst ta) | Inl ([ x ]case q of⦃· x₁ ·⦄ , _ , evals , ta-r)
    = Inl (_ , _ , EFstUnfinished evals (λ ()) , TAFst ta-r)
  progress {Δ} {Σ'} {E = E} {τ = τ} {1+ n} Γ⊢E (TASnd ta)
    with progress Γ⊢E ta
  ... | Inr fails = Inr (EFSnd fails)
  progress {Δ} {Σ'} {E = E} {τ = τ} {1+ n} Γ⊢E (TASnd ta) | Inl (⟨ r1 , r2 ⟩ , _ , evals , TAPair ta-r1 ta-r2)
    = Inl (_ , _ , ESnd evals , ta-r2)
  progress {Δ} {Σ'} {E = E} {τ = τ} {1+ n} Γ⊢E (TASnd ta) | Inl ([ x ]fix x₁ ⦇·λ x₂ => x₃ ·⦈ , _ , evals , TAFix _ ())
  progress {Δ} {Σ'} {E = E} {τ = τ} {1+ n} Γ⊢E (TASnd ta) | Inl ((C⁻[ x ] q) , _ , evals , ta-r)
    = Inl (_ , _ , ESndUnfinished evals (λ ()) , TASnd ta-r)
  progress {Δ} {Σ'} {E = E} {τ = τ} {1+ n} Γ⊢E (TASnd ta) | Inl ([ x ]??[ x₁ ] , _ , evals , ta-r)
    = Inl (_ , _ , ESndUnfinished evals (λ ()) , TASnd ta-r)
  progress {Δ} {Σ'} {E = E} {τ = τ} {1+ n} Γ⊢E (TASnd ta) | Inl ((q ∘ q₁) , _ , evals , ta-r)
    = Inl (_ , _ , ESndUnfinished evals (λ ()) , TASnd ta-r)
  progress {Δ} {Σ'} {E = E} {τ = τ} {1+ n} Γ⊢E (TASnd ta) | Inl (fst q , _ , evals , ta-r)
    = Inl (_ , _ , ESndUnfinished evals (λ ()) , TASnd ta-r)
  progress {Δ} {Σ'} {E = E} {τ = τ} {1+ n} Γ⊢E (TASnd ta) | Inl (snd q , _ , evals , ta-r)
    = Inl (_ , _ , ESndUnfinished evals (λ ()) , TASnd ta-r)
  progress {Δ} {Σ'} {E = E} {τ = τ} {1+ n} Γ⊢E (TASnd ta) | Inl ([ x ]case q of⦃· x₁ ·⦄ , _ , evals , ta-r)
    = Inl (_ , _ , ESndUnfinished evals (λ ()) , TASnd ta-r)
  progress {n = 1+ n} Γ⊢E (TACtor d∈Σ' c∈d ta)
    with progress Γ⊢E ta
  ... | Inr e-fails = Inr (EFCtor e-fails)
  ... | Inl (_ , _ , e-evals , ta-r) = Inl (_ , _ , ECtor e-evals , TACtor d∈Σ' c∈d ta-r)
  progress {Σ' = Σ'} {n = 1+ n} Γ⊢E (TACase d∈σ' e-ta cctx⊆rules h-rules)
    with progress Γ⊢E e-ta
  ... | Inr e-fails = Inr (EFMatchScrut e-fails)
  ... | Inl ([ x ]fix x₁ ⦇·λ x₂ => x₃ ·⦈ , _ , e-evals , TAFix _ ())
  ... | Inl ([ x ]??[ x₁ ] , _ , e-evals , ta-re)
          = Inl (_ , _ , EMatchUnfinished e-evals (λ ()) , TACase d∈σ' Γ⊢E ta-re cctx⊆rules (λ form →
                 let _ , _ , _ , c∈cctx , ec-ta = h-rules form in
                 _ , c∈cctx , ec-ta))
  ... | Inl ((re ∘ re₁) , _ , e-evals , ta-re)
          = Inl (_ , _ , EMatchUnfinished e-evals (λ ()) , TACase d∈σ' Γ⊢E ta-re cctx⊆rules (λ form →
                 let _ , _ , _ , c∈cctx , ec-ta = h-rules form in
                 _ , c∈cctx , ec-ta))
  ... | Inl (fst _ , _ , e-evals , ta-re)
          = Inl (_ , _ , EMatchUnfinished e-evals (λ ()) , TACase d∈σ' Γ⊢E ta-re cctx⊆rules (λ form →
                 let _ , _ , _ , c∈cctx , ec-ta = h-rules form in
                 _ , c∈cctx , ec-ta))
  ... | Inl (snd _ , _ , e-evals , ta-re)
          = Inl (_ , _ , EMatchUnfinished e-evals (λ ()) , TACase d∈σ' Γ⊢E ta-re cctx⊆rules (λ form →
                 let _ , _ , _ , c∈cctx , ec-ta = h-rules form in
                 _ , c∈cctx , ec-ta))
  ... | Inl ([ x ]case re of⦃· x₁ ·⦄ , _ , e-evals , ta-re)
          = Inl (_ , _ , EMatchUnfinished e-evals (λ ()) , TACase d∈σ' Γ⊢E ta-re cctx⊆rules (λ form →
                 let _ , _ , _ , c∈cctx , ec-ta = h-rules form in
                 _ , c∈cctx , ec-ta))
  ... | Inl ((C⁻[ _ ] _) , _ , e-evals , ta-re)
          = Inl (_ , _ , EMatchUnfinished e-evals (λ ()) , TACase d∈σ' Γ⊢E ta-re cctx⊆rules (λ form →
                 let _ , _ , _ , c∈cctx , ec-ta = h-rules form in
                 _ , c∈cctx , ec-ta))
  ... | Inl ((C[ c ] re) , _ , e-evals , TACtor d∈'σ' c∈cctx' ta-re)
    rewrite ctxunicity d∈'σ' d∈σ'
    with π2 (cctx⊆rules (_ , c∈cctx'))
  ... | form
    with h-rules form
  ... | _ , _ , _ , c∈cctx , ec-ta
    rewrite ctxunicity c∈cctx c∈cctx'
    with progress {n = n} (EnvInd Γ⊢E ta-re) ec-ta
  ... | Inr ec-fails = Inr (EFMatchRule CF⛽ form e-evals ec-fails)
  ... | Inl (_ , _ , ec-evals , ta-rec) = Inl (_ , _ , EMatch CF⛽ form e-evals ec-evals , ta-rec)
  progress {n = 1+ n} Γ⊢E (TAHole u∈Δ) = Inl (_ , _ , EHole , TAHole u∈Δ Γ⊢E)
  progress {n = 1+ n} Γ⊢E (TAAsrt _ ta1 ta2)
    with progress Γ⊢E ta1
  ... | Inr e1-fails = Inr (EFAsrtL e1-fails)
  ... | Inl (r1 , _ , e1-evals , ta-r1)
    with progress Γ⊢E ta2
  ... | Inr e2-fails = Inr (EFAsrtR e2-fails)
  ... | Inl (r2 , _ , e2-evals , ta-r2)
    with xc-progress ta-r1 ta-r2
  ... | Inl (_ , c-succ) = Inl (_ , _ , EAsrt e1-evals e2-evals c-succ , TAUnit)
  ... | Inr c-fail       = Inr (EFAsrt e1-evals e2-evals c-fail)

  lemma-xc-no-coerce : ∀{Δ Σ' r1 r2 τ n} →
                         Δ , Σ' ⊢ r1 ·: τ →
                         Δ , Σ' ⊢ r2 ·: τ →
                         r1 ≠ r2 →
                         (∀{ex} → Coerce r1 := ex → ⊥) →
                         r1 ≠ ⟨⟩ →
                         (∀{r'1 r'2} → r1 ≠ ⟨ r'1 , r'2 ⟩) →
                         (∀{c r} → r1 ≠ (C[ c ] r)) →
                         Σ[ k ∈ constraints ] Constraints⦃ r1 , r2 ⦄⌊ ⛽⟨ n ⟩ ⌋:= k
                         ∨ Constraints⦃ r1 , r2 ⦄⌊ ⛽⟨ n ⟩ ⌋:=∅
  lemma-xc-no-coerce ta1 (TAFix x x₁) r1≠r2 no-coerce not-unit not-pair not-ctor
    = Inr (XCFNoCoerce r1≠r2 (Inl not-pair) (Inl not-ctor) no-coerce λ ())
  lemma-xc-no-coerce ta1 (TAApp ta2 ta3) r1≠r2 no-coerce not-unit not-pair not-ctor
    = Inr (XCFNoCoerce r1≠r2 (Inl not-pair) (Inl not-ctor) no-coerce λ ())
  lemma-xc-no-coerce ta1 TAUnit r1≠r2 no-coerce not-unit not-pair not-ctor
    with xb-progress ta1 TAUnit
  ...  | Inl (_ , xb) = Inl (_ , (XCBackProp1 r1≠r2 (Inl not-pair) (Inl not-ctor) CoerceUnit xb))
  ...  | Inr xb-fails = Inr (XCFXB1 r1≠r2 (Inl not-pair) (Inl not-ctor) CoerceUnit xb-fails)
  lemma-xc-no-coerce ta1 ta2@(TAPair _ _) r1≠r2 no-coerce not-unit not-pair not-ctor
    with Coerce-dec
  ...  | Inr nc         = Inr (XCFNoCoerce r1≠r2 (Inl not-pair) (Inl not-ctor) no-coerce λ {c-r2 → nc (_ , c-r2)})
  ...  | Inl (_ , c-r2)
    with xb-progress ta1 (Coerce-preservation ta2 c-r2)
  ...  | Inr xb-fails   = Inr (XCFXB1 r1≠r2 (Inl not-pair) (Inl not-ctor) c-r2 xb-fails)
  ...  | Inl (_ , xb)   = Inl (_ , (XCBackProp1 r1≠r2 (Inl not-pair) (Inl not-ctor) c-r2 xb))
  lemma-xc-no-coerce ta1 (TAFst ta2) r1≠r2 no-coerce not-unit not-pair not-ctor
    = Inr (XCFNoCoerce r1≠r2 (Inl not-pair) (Inl not-ctor) no-coerce λ ())
  lemma-xc-no-coerce ta1 (TASnd ta2) r1≠r2 no-coerce not-unit not-pair not-ctor
    = Inr (XCFNoCoerce r1≠r2 (Inl not-pair) (Inl not-ctor) no-coerce λ ())
  lemma-xc-no-coerce ta1 ta2@(TACtor _ _ _) r1≠r2 no-coerce not-unit not-pair not-ctor
    with Coerce-dec
  ...  | Inr nc         = Inr (XCFNoCoerce r1≠r2 (Inl not-pair) (Inl not-ctor) no-coerce λ {c-r2 → nc (_ , c-r2)})
  ...  | Inl (_ , c-r2)
    with xb-progress ta1 (Coerce-preservation ta2 c-r2)
  ...  | Inr xb-fails   = Inr (XCFXB1 r1≠r2 (Inl not-pair) (Inl not-ctor) c-r2 xb-fails)
  ...  | Inl (_ , xb)   = Inl (_ , (XCBackProp1 r1≠r2 (Inl not-pair) (Inl not-ctor) c-r2 xb))
  lemma-xc-no-coerce ta1 (TAUnwrapCtor x x₁ ta2) r1≠r2 no-coerce not-unit not-pair not-ctor
    = Inr (XCFNoCoerce r1≠r2 (Inl not-pair) (Inl not-ctor) no-coerce λ ())
  lemma-xc-no-coerce ta1 (TACase x x₁ ta2 x₂ x₃) r1≠r2 no-coerce not-unit not-pair not-ctor
    = Inr (XCFNoCoerce r1≠r2 (Inl not-pair) (Inl not-ctor) no-coerce λ ())
  lemma-xc-no-coerce ta1 (TAHole x x₁) r1≠r2 no-coerce not-unit not-pair not-ctor
    = Inr (XCFNoCoerce r1≠r2 (Inl not-pair) (Inl not-ctor) no-coerce λ ())

  xc-progress {r1 = r1} {r2} ta1 ta2
    with result-==-dec r1 r2
  ... | Inl refl = Inl (_ , XCExRefl)
  xc-progress {r1 = _} {_} ta1@(TAFix x x₁) ta2 | Inr r1≠r2
    = lemma-xc-no-coerce ta1 ta2 r1≠r2 (λ ()) (λ ()) (λ ()) λ ()
  xc-progress {r1 = _} {_} ta1@(TAApp _ _) ta2 | Inr r1≠r2
    = lemma-xc-no-coerce ta1 ta2 r1≠r2 (λ ()) (λ ()) (λ ()) λ ()
  xc-progress {r1 = _} {_} TAUnit ta2 | Inr r1≠r2
    with xb-progress ta2 TAUnit
  ...  | Inl (_ , xb) = Inl (_ , (XCBackProp2 r1≠r2 (Inl (λ ())) (Inl (λ ())) CoerceUnit xb))
  ...  | Inr xb-fails = Inr (XCFXB2 r1≠r2 (Inl (λ ())) (Inl (λ ())) CoerceUnit xb-fails)
  xc-progress (TAPair ta1a ta1b) (TAPair ta2a ta2b) | Inr r1≠r2
    with xc-progress ta1a ta2a
  ...  | Inr xca-fails = Inr (XCFPair1 xca-fails)
  ...  | Inl (_ , xca)
    with xc-progress ta1b ta2b
  ...  | Inr xcb-fails = Inr (XCFPair2 xcb-fails)
  ...  | Inl (_ , xcb) = Inl (_ , XCPair r1≠r2 xca xcb)
  xc-progress ta1@(TAPair _ _) ta2@(TAApp _ _) | Inr r1≠r2
    with Coerce-dec
  ...  | Inr nc         = Inr (XCFNoCoerce r1≠r2 (Inr (λ ())) (Inr (λ ())) (λ {c-r1 → nc (_ , c-r1)}) λ ())
  ...  | Inl (_ , c-r1)
    with xb-progress ta2 (Coerce-preservation ta1 c-r1)
  ...  | Inr xb-fails   = Inr (XCFXB2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb-fails)
  ...  | Inl (_ , xb)   = Inl (_ , (XCBackProp2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb))
  xc-progress ta1@(TAPair _ _) ta2@(TAFst _) | Inr r1≠r2
    with Coerce-dec
  ...  | Inr nc         = Inr (XCFNoCoerce r1≠r2 (Inr (λ ())) (Inr (λ ())) (λ {c-r1 → nc (_ , c-r1)}) λ ())
  ...  | Inl (_ , c-r1)
    with xb-progress ta2 (Coerce-preservation ta1 c-r1)
  ...  | Inr xb-fails   = Inr (XCFXB2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb-fails)
  ...  | Inl (_ , xb)   = Inl (_ , (XCBackProp2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb))
  xc-progress ta1@(TAPair _ _) ta2@(TASnd _) | Inr r1≠r2
    with Coerce-dec
  ...  | Inr nc         = Inr (XCFNoCoerce r1≠r2 (Inr (λ ())) (Inr (λ ())) (λ {c-r1 → nc (_ , c-r1)}) λ ())
  ...  | Inl (_ , c-r1)
    with xb-progress ta2 (Coerce-preservation ta1 c-r1)
  ...  | Inr xb-fails   = Inr (XCFXB2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb-fails)
  ...  | Inl (_ , xb)   = Inl (_ , (XCBackProp2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb))
  xc-progress ta1@(TAPair _ _) ta2@(TAUnwrapCtor _ _ _) | Inr r1≠r2
    with Coerce-dec
  ...  | Inr nc         = Inr (XCFNoCoerce r1≠r2 (Inr (λ ())) (Inr (λ ())) (λ {c-r1 → nc (_ , c-r1)}) λ ())
  ...  | Inl (_ , c-r1)
    with xb-progress ta2 (Coerce-preservation ta1 c-r1)
  ...  | Inr xb-fails   = Inr (XCFXB2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb-fails)
  ...  | Inl (_ , xb)   = Inl (_ , (XCBackProp2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb))
  xc-progress ta1@(TAPair _ _) ta2@(TACase _ _ _ _ _) | Inr r1≠r2
    with Coerce-dec
  ...  | Inr nc         = Inr (XCFNoCoerce r1≠r2 (Inr (λ ())) (Inr (λ ())) (λ {c-r1 → nc (_ , c-r1)}) λ ())
  ...  | Inl (_ , c-r1)
    with xb-progress ta2 (Coerce-preservation ta1 c-r1)
  ...  | Inr xb-fails   = Inr (XCFXB2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb-fails)
  ...  | Inl (_ , xb)   = Inl (_ , (XCBackProp2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb))
  xc-progress ta1@(TAPair _ _) ta2@(TAHole _ _) | Inr r1≠r2
    with Coerce-dec
  ...  | Inr nc         = Inr (XCFNoCoerce r1≠r2 (Inr (λ ())) (Inr (λ ())) (λ {c-r1 → nc (_ , c-r1)}) λ ())
  ...  | Inl (_ , c-r1)
    with xb-progress ta2 (Coerce-preservation ta1 c-r1)
  ...  | Inr xb-fails   = Inr (XCFXB2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb-fails)
  ...  | Inl (_ , xb)   = Inl (_ , (XCBackProp2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb))
  xc-progress ta1@(TAFst _) ta2 | Inr r1≠r2
    = lemma-xc-no-coerce ta1 ta2 r1≠r2 (λ ()) (λ ()) (λ ()) λ ()
  xc-progress {r1 = _} {_} ta1@(TASnd _) ta2 | Inr r1≠r2
    = lemma-xc-no-coerce ta1 ta2 r1≠r2 (λ ()) (λ ()) (λ ()) λ ()
  xc-progress (TACtor {c = c1} d∈σ1 c1∈cctx ta1) (TACtor {c = c2} d∈σ2 c2∈cctx ta2) | Inr r1≠r2
    with natEQ c1 c2
  ...  | Inr ne         = Inr (XCFCtorMM ne)
  ...  | Inl refl
    rewrite ctxunicity d∈σ1 d∈σ2 | ctxunicity c1∈cctx c2∈cctx
    with xc-progress ta1 ta2
  ...  | Inr xc-fails   = Inr (XCFCtor xc-fails)
  ...  | Inl (_ , xc)   = Inl (_ , XCCtor (λ where refl → r1≠r2 refl) xc)
  xc-progress ta1@(TACtor _ _ _) ta2@(TAApp _ _) | Inr r1≠r2
    with Coerce-dec
  ...  | Inr nc         = Inr (XCFNoCoerce r1≠r2 (Inr (λ ())) (Inr (λ ())) (λ {c-r1 → nc (_ , c-r1)}) λ ())
  ...  | Inl (_ , c-r1)
    with xb-progress ta2 (Coerce-preservation ta1 c-r1)
  ...  | Inr xb-fails   = Inr (XCFXB2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb-fails)
  ...  | Inl (_ , xb)   = Inl (_ , (XCBackProp2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb))
  xc-progress ta1@(TACtor _ _ _) ta2@(TAFst _) | Inr r1≠r2
    with Coerce-dec
  ...  | Inr nc         = Inr (XCFNoCoerce r1≠r2 (Inr (λ ())) (Inr (λ ())) (λ {c-r1 → nc (_ , c-r1)}) λ ())
  ...  | Inl (_ , c-r1)
    with xb-progress ta2 (Coerce-preservation ta1 c-r1)
  ...  | Inr xb-fails   = Inr (XCFXB2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb-fails)
  ...  | Inl (_ , xb)   = Inl (_ , (XCBackProp2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb))
  xc-progress ta1@(TACtor _ _ _) ta2@(TASnd _) | Inr r1≠r2
    with Coerce-dec
  ...  | Inr nc         = Inr (XCFNoCoerce r1≠r2 (Inr (λ ())) (Inr (λ ())) (λ {c-r1 → nc (_ , c-r1)}) λ ())
  ...  | Inl (_ , c-r1)
    with xb-progress ta2 (Coerce-preservation ta1 c-r1)
  ...  | Inr xb-fails   = Inr (XCFXB2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb-fails)
  ...  | Inl (_ , xb)   = Inl (_ , (XCBackProp2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb))
  xc-progress ta1@(TACtor _ _ _) ta2@(TAUnwrapCtor _ _ _) | Inr r1≠r2
    with Coerce-dec
  ...  | Inr nc         = Inr (XCFNoCoerce r1≠r2 (Inr (λ ())) (Inr (λ ())) (λ {c-r1 → nc (_ , c-r1)}) λ ())
  ...  | Inl (_ , c-r1)
    with xb-progress ta2 (Coerce-preservation ta1 c-r1)
  ...  | Inr xb-fails   = Inr (XCFXB2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb-fails)
  ...  | Inl (_ , xb)   = Inl (_ , (XCBackProp2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb))
  xc-progress ta1@(TACtor _ _ _) ta2@(TACase _ _ _ _ _) | Inr r1≠r2
    with Coerce-dec
  ...  | Inr nc         = Inr (XCFNoCoerce r1≠r2 (Inr (λ ())) (Inr (λ ())) (λ {c-r1 → nc (_ , c-r1)}) λ ())
  ...  | Inl (_ , c-r1)
    with xb-progress ta2 (Coerce-preservation ta1 c-r1)
  ...  | Inr xb-fails   = Inr (XCFXB2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb-fails)
  ...  | Inl (_ , xb)   = Inl (_ , (XCBackProp2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb))
  xc-progress ta1@(TACtor _ _ _) ta2@(TAHole _ _) | Inr r1≠r2
    with Coerce-dec
  ...  | Inr nc         = Inr (XCFNoCoerce r1≠r2 (Inr (λ ())) (Inr (λ ())) (λ {c-r1 → nc (_ , c-r1)}) λ ())
  ...  | Inl (_ , c-r1)
    with xb-progress ta2 (Coerce-preservation ta1 c-r1)
  ...  | Inr xb-fails   = Inr (XCFXB2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb-fails)
  ...  | Inl (_ , xb)   = Inl (_ , (XCBackProp2 r1≠r2 (Inr (λ ())) (Inr (λ ())) c-r1 xb))
  xc-progress {r1 = _} {_} ta1@(TAUnwrapCtor _ _ _) ta2 | Inr r1≠r2
    = lemma-xc-no-coerce ta1 ta2 r1≠r2 (λ ()) (λ ()) (λ ()) λ ()
  xc-progress {r1 = _} {_} ta1@(TACase _ _ _ _ _) ta2 | Inr r1≠r2
    = lemma-xc-no-coerce ta1 ta2 r1≠r2 (λ ()) (λ ()) (λ ()) λ ()
  xc-progress {r1 = _} {_} ta1@(TAHole _ _) ta2 | Inr r1≠r2
    = lemma-xc-no-coerce ta1 ta2 r1≠r2 (λ ()) (λ ()) (λ ()) λ ()

  xb-progress {n = Z} _ _ = Inl (_ , XBLimit)
  xb-progress {ex = ex} {n = 1+ n} ta-r ta-ex
    with ex-¿¿-dec {ex}
  ... | Inl refl = Inl (_ , XBNone)
  xb-progress {n = 1+ n} ta-f@(TAFix Γ⊢E (TAFix ta-e)) (TAMap _ ta-v ta-ex) | Inr ne
    with progress {n = n} (EnvInd (EnvInd Γ⊢E ta-f) ta-v) ta-e
  ... | Inr fails    = Inr (XBFFixEval CF⛽ refl fails)
  ... | Inl (_ , _ , evals , ta)
    with xb-progress {n = n} ta ta-ex
  ... | Inr fails    = Inr (XBFFix CF⛽ refl evals fails)
  ... | Inl (_ , xb) = Inl (_ , XBFix CF⛽ refl evals xb)
  xb-progress (TAFix x (TAFix _)) TADC | Inr ne = Inl (_ , XBNone)
  xb-progress (TAApp {arg = v} ta-rf ta-rarg) ta-ex | Inr ne
    with value-dec {v}
  ... | Inr nv  = Inr (XBFAppNonVal ne nv)
  ... | Inl val
    with xb-progress ta-rf (TAMap val ta-rarg ta-ex)
  ... | Inr fails    = Inr (XBFApp ne val fails)
  ... | Inl (_ , xb) = Inl (_ , XBApp ne val xb)
  xb-progress TAUnit TAUnit | Inr ne = Inl (_ , XBUnit)
  xb-progress TAUnit TADC   | Inr ne = Inl (_ , XBNone)
  xb-progress (TAPair ta-r1 ta-r2) (TAPair ta-ex1 ta-ex2) | Inr ne
    with xb-progress ta-r1 ta-ex1
  ... | Inr fails     = Inr (XBFPair1 fails)
  ... | Inl (_ , xb1)
    with xb-progress ta-r2 ta-ex2
  ... | Inr fails     = Inr (XBFPair2 fails)
  ... | Inl (_ , xb2) = Inl (_ , XBPair xb1 xb2)
  xb-progress (TAPair ta-r1 ta-r2) TADC | Inr ne = Inl (_ , XBNone)
  xb-progress (TAFst ta-r) ta-ex | Inr ne
    with xb-progress ta-r (TAPair ta-ex TADC)
  ... | Inr fails    = Inr (XBFFst ne fails)
  ... | Inl (_ , xb) = Inl (_ , XBFst ne xb)
  xb-progress (TASnd ta-r) ta-ex | Inr ne
    with xb-progress ta-r (TAPair TADC ta-ex)
  ... | Inr fails    = Inr (XBFSnd ne fails)
  ... | Inl (_ , xb) = Inl (_ , XBSnd ne xb)
  xb-progress (TACtor {c = c1} h1a h1b ta-r) (TACtor {c = c2} h2a h2b ta-ex) | Inr ne
    with natEQ c1 c2
  ... | Inr ne'  = Inr (XBFCtorMM ne')
  ... | Inl refl
    rewrite ctxunicity h1a h2a | ctxunicity h1b h2b
    with xb-progress ta-r ta-ex
  ... | Inr fails    = Inr (XBFCtor fails)
  ... | Inl (_ , xb) = Inl (_ , XBCtor xb)
  xb-progress (TACtor x x₁ ta-r) TADC | Inr ne = Inl (_ , XBNone)
  xb-progress (TAUnwrapCtor h1 h2 ta-r) ta-ex | Inr ne
    with xb-progress ta-r (TACtor h1 h2 ta-ex)
  ... | Inr fails    = Inr (XBFUnwrapCtor ne fails)
  ... | Inl (_ , xb) = Inl (_ , XBUnwrapCtor ne xb)
  xb-progress {n = 1+ n} ta-C@(TACase {rules = rules} x x₁ ta-r x₂ x₃) ta-ex | Inr ne
    = lemma-xb-progress-case {n = 1+ n} {n} refl ∥ rules ∥ rules refl ∅ (λ y → y) (λ ()) Inl ta-C ta-ex ne
  xb-progress (TAHole x x₁) TAUnit | Inr ne
    = Inl (_ , XBHole ne λ ())
  xb-progress (TAHole x x₁) (TAPair ta-ex ta-ex₁) | Inr ne
    = Inl (_ , XBHole ne λ ())
  xb-progress (TAHole x x₁) (TACtor x₂ x₃ ta-ex) | Inr ne
    = Inl (_ , XBHole ne λ ())
  xb-progress (TAHole x x₁) TADC | Inr ne = Inl (_ , XBNone)
  xb-progress (TAHole x x₁) (TAMap x₂ x₃ ta-ex) | Inr ne
    = Inr XBFHole

  lemma-xb-progress-case {E = E} {r} {rules} {ex} {n = n} {n↓} refl Z [] len-unchecked failed unchecked-wf failed-wf exh ta-C ta-ex n¿¿
    = Inr (XBFMatch CF⛽ n¿¿ all-failed)
      where
        all-failed : ∀{c-j x-j : Nat} {e-j : exp} →
                       (c-j , |C x-j => e-j) ∈ rules →
                       r ⇐ C[ c-j ] ¿¿ ⌊ ⛽⟨ n ⟩ ⌋:=∅
                       ∨ Σ[ k1 ∈ constraints ] (
                             r ⇐ C[ c-j ] ¿¿ ⌊ ⛽⟨ n ⟩ ⌋:= k1 ∧ (E ,, (x-j , C⁻[ c-j ] r)) ⊢ e-j ⌊ ⛽⟨ n↓ ⟩ ⌋⇒∅)
                       ∨ Σ[ k1 ∈ constraints ] Σ[ k2 ∈ constraints ] Σ[ r-j ∈ result ] (
                             r ⇐ C[ c-j ] ¿¿ ⌊ ⛽⟨ n ⟩ ⌋:= k1 ∧ (E ,, (x-j , C⁻[ c-j ] r)) ⊢ e-j ⌊ ⛽⟨ n↓ ⟩ ⌋⇒ r-j ⊣ k2 ∧ r-j ⇐ ex ⌊ ⛽⟨ n↓ ⟩ ⌋:=∅)
        all-failed c-j∈rules
          with exh (_ , c-j∈rules)
        ... | Inl (_ , ())
        ... | Inr ((c-j , x-j , e-j , p-j) , c-j∈f)
          with failed-wf c-j∈f
        ... | refl , c-j∈'rules
          with ctxunicity c-j∈rules c-j∈'rules
        ... | refl = p-j
  lemma-xb-progress-case {n = 1+ n↓} {n↓} refl (1+ len) unchecked len-unchecked failed unchecked-wf failed-wf exh ta-C@(TACase {rules = rules} d∈σ' Γ⊢E ta-r _ ta-rules) ta-ex n¿¿
    with ctx-elim {Γ = unchecked}
  ... | Inl refl = abort (0≠1+n (! len-unchecked))
  ... | Inr (c , |C x-j => e-j , unchecked' , refl , c#unchecked')
    with unchecked-wf (x,a∈Γ,,x,a {Γ = unchecked'})
  ... | c∈rules
    with ta-rules c∈rules
  ... | _ , c∈cctx , ta-be
    with xb-progress ta-r (TACtor d∈σ' c∈cctx TADC)
  ... | Inr fails
          = lemma-xb-progress-case
              refl
              len
              unchecked'
              (1+inj (len-unchecked · ctx-decreasing c#unchecked'))
              (failed ,, (c , fail))
              unchecked-wf' failed-wf' exh' ta-C ta-ex n¿¿
            where
              fail = c , x-j , e-j , (Inl fails)
              unchecked-wf' : ∀{c' rule'} → (c' , rule') ∈ unchecked' → (c' , rule') ∈ rules
              unchecked-wf' {c' = c'} c'∈uc'
                with natEQ c c'
              ... | Inl refl = abort (c#unchecked' (_ , c'∈uc'))
              ... | Inr cne  = unchecked-wf (x∈Γ→x∈Γ+ (flip cne) c'∈uc')
              failed-wf' : ∀{c' c-j' x-j' e-j' p-j'} →
                             (c' , c-j' , x-j' , e-j' , p-j') ∈ (failed ,, (c , fail)) →
                             c' == c-j' ∧ ((c' , (|C x-j' => e-j')) ∈ rules)
              failed-wf' {c' = c'} {c-j'} c'∈f+
                with natEQ c c'
              ... | Inr cne  = failed-wf (x∈Γ+→x∈Γ (flip cne) c'∈f+)
              ... | Inl refl
                with ctxunicity c'∈f+ (x,a∈Γ,,x,a {Γ = failed})
              ... | refl = refl , c∈rules
              exh' : ∀{c'} → dom rules c' → dom unchecked' c' ∨ dom (failed ,, (c , fail)) c'
              exh' {c' = c'} c'∈rules
                with natEQ c c'
              ... | Inl refl = Inr (_ , x,a∈Γ,,x,a {Γ = failed})
              ... | Inr cne
                with exh c'∈rules
              ... | Inl (_ , c'∈uc) = Inl (_ , (x∈Γ+→x∈Γ (flip cne) c'∈uc))
              ... | Inr (_ , c'∈f)  = Inr (_ , x∈Γ→x∈Γ+ (flip cne) c'∈f)
  ... | Inl (_ , xb-r)
    with progress {n = n↓} (EnvInd Γ⊢E (TAUnwrapCtor d∈σ' c∈cctx ta-r)) ta-be
  ... | Inr fails
          = lemma-xb-progress-case
              refl
              len
              unchecked'
              (1+inj (len-unchecked · ctx-decreasing c#unchecked'))
              (failed ,, (c , fail))
              unchecked-wf' failed-wf' exh' ta-C ta-ex n¿¿
            where
              fail = c , x-j , e-j , (Inr (Inl (_ , xb-r , fails)))
              unchecked-wf' : ∀{c' rule'} → (c' , rule') ∈ unchecked' → (c' , rule') ∈ rules
              unchecked-wf' {c' = c'} c'∈uc'
                with natEQ c c'
              ... | Inl refl = abort (c#unchecked' (_ , c'∈uc'))
              ... | Inr cne  = unchecked-wf (x∈Γ→x∈Γ+ (flip cne) c'∈uc')
              failed-wf' : ∀{c' c-j' x-j' e-j' p-j'} →
                             (c' , c-j' , x-j' , e-j' , p-j') ∈ (failed ,, (c , fail)) →
                             c' == c-j' ∧ ((c' , (|C x-j' => e-j')) ∈ rules)
              failed-wf' {c' = c'} {c-j'} c'∈f+
                with natEQ c c'
              ... | Inr cne  = failed-wf (x∈Γ+→x∈Γ (flip cne) c'∈f+)
              ... | Inl refl
                with ctxunicity c'∈f+ (x,a∈Γ,,x,a {Γ = failed})
              ... | refl = refl , c∈rules
              exh' : ∀{c'} → dom rules c' → dom unchecked' c' ∨ dom (failed ,, (c , fail)) c'
              exh' {c' = c'} c'∈rules
                with natEQ c c'
              ... | Inl refl = Inr (_ , x,a∈Γ,,x,a {Γ = failed})
              ... | Inr cne
                with exh c'∈rules
              ... | Inl (_ , c'∈uc) = Inl (_ , (x∈Γ+→x∈Γ (flip cne) c'∈uc))
              ... | Inr (_ , c'∈f)  = Inr (_ , x∈Γ→x∈Γ+ (flip cne) c'∈f)
  ... | Inl (_ , _ , evals , ta-br)
    with xb-progress {n = n↓} ta-br ta-ex
  ... | Inr fails
          = lemma-xb-progress-case
              refl
              len
              unchecked'
              (1+inj (len-unchecked · ctx-decreasing c#unchecked'))
              (failed ,, (c , fail))
              unchecked-wf' failed-wf' exh' ta-C ta-ex n¿¿
            where
              fail = c , x-j , e-j , (Inr (Inr (_ , _ , _ , xb-r , evals , fails)))
              unchecked-wf' : ∀{c' rule'} → (c' , rule') ∈ unchecked' → (c' , rule') ∈ rules
              unchecked-wf' {c' = c'} c'∈uc'
                with natEQ c c'
              ... | Inl refl = abort (c#unchecked' (_ , c'∈uc'))
              ... | Inr cne  = unchecked-wf (x∈Γ→x∈Γ+ (flip cne) c'∈uc')
              failed-wf' : ∀{c' c-j' x-j' e-j' p-j'} →
                             (c' , c-j' , x-j' , e-j' , p-j') ∈ (failed ,, (c , fail)) →
                             c' == c-j' ∧ ((c' , (|C x-j' => e-j')) ∈ rules)
              failed-wf' {c' = c'} {c-j'} c'∈f+
                with natEQ c c'
              ... | Inr cne  = failed-wf (x∈Γ+→x∈Γ (flip cne) c'∈f+)
              ... | Inl refl
                with ctxunicity c'∈f+ (x,a∈Γ,,x,a {Γ = failed})
              ... | refl = refl , c∈rules
              exh' : ∀{c'} → dom rules c' → dom unchecked' c' ∨ dom (failed ,, (c , fail)) c'
              exh' {c' = c'} c'∈rules
                with natEQ c c'
              ... | Inl refl = Inr (_ , x,a∈Γ,,x,a {Γ = failed})
              ... | Inr cne
                with exh c'∈rules
              ... | Inl (_ , c'∈uc) = Inl (_ , (x∈Γ+→x∈Γ (flip cne) c'∈uc))
              ... | Inr (_ , c'∈f)  = Inr (_ , x∈Γ→x∈Γ+ (flip cne) c'∈f)
  ... | Inl (_ , xb)
          = Inl (_ , (XBMatch CF⛽ n¿¿ c∈rules xb-r evals xb))

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
