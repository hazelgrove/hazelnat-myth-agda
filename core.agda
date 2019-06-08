open import Nat
open import Prelude
open import List
open import contexts

module core where
  -- types
  data typ : Set where
    _==>_ : typ → typ → typ
    ⟨_⟩   : List typ → typ
    D[_]  : Nat → typ

  -- arrow type constructors bind very tightly
  infixr 25  _==>_

  tctx = typ ctx
  hctx = (tctx ∧ typ) ctx
  denv = Σ[ dctx ∈ tctx ctx ]
    ∀{d1 d2 cctx1 cctx2 c} →
    d1 ≠ d2 →
    (d1 , cctx1) ∈ dctx →
    (d2 , cctx2) ∈ dctx →
    c # cctx1 ∨ c # cctx2

  mutual
    -- examples
    data ex : Set where
      PF    : pf → ex
      ⟨_⟩   : List ex → ex
      C[_]_ : Nat → ex → ex

    -- partial functions
    pf = List (result ∧ ex)

    data _ex-complete : ex → Set where
      EXCPF   : ∀{pf} → pf pf-complete → (PF pf) ex-complete
      EXCTpl  : ∀{exs} → (∀{i} → (i<∥exs∥ : i < ∥ exs ∥) → exs ⟦ i given i<∥exs∥ ⟧ ex-complete) → ⟨ exs ⟩ ex-complete
      EXCCtor : ∀{c ex} → ex ex-complete → (C[ c ] ex) ex-complete

    data _pf-complete : pf → Set where
      PFC : ∀{pf} →
              (∀{i r ex} →
                 (i<∥pf∥ : i < ∥ pf ∥) →
                 (r , ex) == pf ⟦ i given i<∥pf∥ ⟧ →
                 r rcomplete ∧ ex ex-complete) →
              pf pf-complete

    data _ex-value : ex → Set where
      EXVPF   : ∀{pf} → pf pf-value → (PF pf) ex-value
      EXVTpl  : ∀{exs} → (∀{i} → (i<∥exs∥ : i < ∥ exs ∥) → exs ⟦ i given i<∥exs∥ ⟧ ex-value) → ⟨ exs ⟩ ex-value
      EXVCtor : ∀{c ex} → ex ex-value → (C[ c ] ex) ex-value

    data _pf-value : pf → Set where
      PFV : ∀{pf} →
              (∀{i v ex} →
                 (i<∥pf∥ : i < ∥ pf ∥) →
                 (v , ex) == pf ⟦ i given i<∥pf∥ ⟧ →
                 v value ∧ ex ex-value) →
              pf pf-value

    data _ex-final : ex → Set where
      EXFPF   : ∀{pf} → pf pf-final → (PF pf) ex-final
      EXFTpl  : ∀{exs} → (∀{i} → (i<∥exs∥ : i < ∥ exs ∥) → exs ⟦ i given i<∥exs∥ ⟧ ex-final) → ⟨ exs ⟩ ex-final
      EXFCtor : ∀{c ex} → ex ex-final → (C[ c ] ex) ex-final

    data _pf-final : pf → Set where
      PFF : ∀{pf} →
              (∀{i f ex} →
                 (i<∥pf∥ : i < ∥ pf ∥) →
                 (f , ex) == pf ⟦ i given i<∥pf∥ ⟧ →
                 f final ∧ ex ex-final) →
              pf pf-final

    -- type assignment for examples. only complete examples can type-check
    data _⊢_:·_ : denv → ex → typ → Set where
      TATpl  : ∀{Σ' exs τs} →
                 ∥ exs ∥ == ∥ τs ∥ →
                 (∀{i} →
                    (i<∥exs∥ : i < ∥ exs ∥) →
                    (i<∥τs∥ : i < ∥ τs ∥) →
                    Σ' ⊢ exs ⟦ i given i<∥exs∥ ⟧ :· (τs ⟦ i given i<∥τs∥ ⟧)) →
                 Σ' ⊢ ⟨ exs ⟩ :· ⟨ τs ⟩
      TACtor : ∀{Σ' d cctx c ex τ} →
                 (d , cctx) ∈ π1 Σ' →
                 (c , τ) ∈ cctx →
                 Σ' ⊢ ex :· τ →
                 Σ' ⊢ C[ c ] ex :· D[ d ]
      TAPF   : ∀{Σ' pf τ1 τ2} →
                 (∀{i v ex} →
                    (i<∥pf∥ : i < ∥ pf ∥) →
                    (v , ex) == pf ⟦ i given i<∥pf∥ ⟧ →
                    v value ∧ (∅ , Σ' ⊢ v ·: τ1) ∧ Σ' ⊢ ex :· τ2) →
                 Σ' ⊢ PF pf :· τ1 ==> τ2

    record rule : Set where
      inductive
      constructor |C_=>_
      field
        parm   : Nat
        branch : exp

    -- Expressions (Sketches)
    data exp : Set where
      ·λ_=>_        : Nat → exp → exp
      fix_⦇·λ_=>_·⦈ : Nat → Nat → exp → exp
      X[_]          : Nat → exp
      _∘_           : exp → exp → exp
      ⟨_⟩           : List exp → exp
      get[_th-of_]_ : Nat → Nat → exp → exp
      C[_]_         : Nat → exp → exp
      case_of⦃·_·⦄ : exp → rule ctx → exp
      ??[_]         : Nat → exp
      PF            : pf → exp
      PBE:assert    : exp → exp → exp

    data hole-name-new : (e : exp) → (u : Nat) → Set where
      HNNLam  : ∀{x e u} → hole-name-new e u → hole-name-new (·λ x => e) u
      HNNFix  : ∀{x f e u} → hole-name-new e u → hole-name-new (fix f ⦇·λ x => e ·⦈) u
      HNNVar  : ∀{x u} → hole-name-new (X[ x ]) u
      HNNAp   : ∀{e1 e2 u} → hole-name-new e1 u → hole-name-new e2 u → hole-name-new (e1 ∘ e2) u
      HNNTup  : ∀{es u} → (∀{i} → (h : i < ∥ es ∥) → hole-name-new (es ⟦ i given h ⟧) u) → hole-name-new ⟨ es ⟩ u
      HNNGet  : ∀{i n e u} → hole-name-new e u → hole-name-new (get[ i th-of n ] e) u
      HNNCtor : ∀{c e u} → hole-name-new e u → hole-name-new (C[ c ] e) u
      HNNCase : ∀{e rules u} →
                  hole-name-new e u →
                  (∀{c rule} → (c , rule) ∈ rules → hole-name-new (rule.branch rule) u) →
                  hole-name-new (case e of⦃· rules ·⦄) u
      HNNHole : ∀{u' u} → u' ≠ u → hole-name-new (??[ u' ]) u
      -- pf shouldn't be incomplete, so we don't define a case for incomplete pfs in which the hole would
      -- nonetheless be new
      HNNPF   : ∀{pf u} → pf pf-complete → hole-name-new (PF pf) u
      HNNAsrt : ∀{e1 e2 u} → hole-name-new e1 u → hole-name-new e2 u → hole-name-new (PBE:assert e1 e2) u

    data holes-disjoint : (e1 : exp) → (e2 : exp) → Set where
      HDLam  : ∀{x e e'} → holes-disjoint e e' → holes-disjoint (·λ x => e) e'
      HDFix  : ∀{x f e e'} → holes-disjoint e e' → holes-disjoint (fix f ⦇·λ x => e ·⦈) e'
      HDVar  : ∀{x e'} → holes-disjoint (X[ x ]) e'
      HDAp   : ∀{e1 e2 e'} → holes-disjoint e1 e' → holes-disjoint e2 e' → holes-disjoint (e1 ∘ e2) e'
      HDTup  : ∀{es e'} → (∀{i} → (h : i < ∥ es ∥) → holes-disjoint (es ⟦ i given h ⟧) e') → holes-disjoint ⟨ es ⟩ e'
      HDGet  : ∀{i n e e'} → holes-disjoint e e' → holes-disjoint (get[ i th-of n ] e) e'
      HDCtor : ∀{c e e'} → holes-disjoint e e' → holes-disjoint (C[ c ] e) e'
      HDCase : ∀{e rules e'} →
                 holes-disjoint e e' →
                 (∀{c rule} → (c , rule) ∈ rules → holes-disjoint (rule.branch rule) e') →
                 holes-disjoint (case e of⦃· rules ·⦄) e'
      HDHole : ∀{u e'} → hole-name-new e' u → holes-disjoint (??[ u ]) e'
      -- pf shouldn't be incomplete, so we don't define a case for incomplete pfs in which the holes would
      -- nonetheless be disjoint
      HDPF   : ∀{pf e'} → pf pf-complete → holes-disjoint (PF pf) e'
      HDAsrt : ∀{e1 e2 e'} → holes-disjoint e1 e' → holes-disjoint e2 e' → holes-disjoint (PBE:assert e1 e2) e'

    data _ecomplete : exp → Set where
      ECLam  : ∀{x e} → e ecomplete → (·λ x => e) ecomplete
      ECFix  : ∀{f x e} → e ecomplete → fix f ⦇·λ x => e ·⦈ ecomplete
      ECVar  : ∀{x} → X[ x ] ecomplete
      ECAp   : ∀{e1 e2} → e1 ecomplete → e2 ecomplete → (e1 ∘ e2) ecomplete
      ECTpl  : ∀{es} → (∀{i} → (i<∥es∥ : i < ∥ es ∥) → es ⟦ i given i<∥es∥ ⟧ ecomplete) → ⟨ es ⟩ ecomplete
      ECGet  : ∀{i n e} → e ecomplete → (get[ i th-of n ] e) ecomplete
      ECCtor : ∀{c e} → e ecomplete → (C[ c ] e) ecomplete
      ECCase : ∀{e rules} →
                 e ecomplete →
                 (∀{c rule} → (c , rule) ∈ rules → (rule.branch rule) ecomplete) →
                 case e of⦃· rules ·⦄ ecomplete
      ECPF   : ∀{pf} → pf pf-complete → (PF pf) ecomplete
      ECAsrt : ∀{e1 e2} → e1 ecomplete → e2 ecomplete → (PBE:assert e1 e2) ecomplete

    -- type assignment for expressions
    data _,_,_⊢_::_ : hctx → denv → tctx → exp → typ → Set where
      TALam  : ∀{Δ Σ' Γ x e τ1 τ2} →
                 x # Γ →
                 Δ , Σ' , (Γ ,, (x , τ1)) ⊢ e :: τ2 →
                 Δ , Σ' , Γ ⊢ ·λ x => e :: τ1 ==> τ2
      TAFix  : ∀{Δ Σ' Γ f x e τ1 τ2} →
                 f # Γ →
                 x # Γ →
                 Δ , Σ' , (Γ ,, (f , τ1 ==> τ2) ,, (x , τ1)) ⊢ e :: τ2 →
                 Δ , Σ' , Γ ⊢ fix f ⦇·λ x => e ·⦈ :: τ1 ==> τ2
      TAVar  : ∀{Δ Σ' Γ x τ} → (x , τ) ∈ Γ → Δ , Σ' , Γ ⊢ X[ x ] :: τ
      TAApp  : ∀{Δ Σ' Γ f arg τ1 τ2} →
                 holes-disjoint f arg →
                 Δ , Σ' , Γ ⊢ f :: τ1 ==> τ2 →
                 Δ , Σ' , Γ ⊢ arg :: τ1 →
                 Δ , Σ' , Γ ⊢ f ∘ arg :: τ2
      TATpl  : ∀{Δ Σ' Γ es τs} →
                 ∥ es ∥ == ∥ τs ∥ →
                 (∀{i j} →
                    (i<∥es∥ : i < ∥ es ∥) →
                    (j<∥es∥ : j < ∥ es ∥) →
                    i ≠ j →
                    holes-disjoint (es ⟦ i given i<∥es∥ ⟧) (es ⟦ j given j<∥es∥ ⟧)) →
                 (∀{i} →
                    (i<∥es∥ : i < ∥ es ∥) →
                    (i<∥τs∥ : i < ∥ τs ∥) →
                    Δ , Σ' , Γ ⊢ es ⟦ i given i<∥es∥ ⟧ :: (τs ⟦ i given i<∥τs∥ ⟧)) →
                 Δ , Σ' , Γ ⊢ ⟨ es ⟩ :: ⟨ τs ⟩
      TAGet  : ∀{Δ Σ' Γ i n e τs} →
                 n == ∥ τs ∥ → -- this awkwardness is necessary to permit unification
                 (i<∥τs∥ : i < ∥ τs ∥) →
                 Δ , Σ' , Γ ⊢ e :: ⟨ τs ⟩ →
                 Δ , Σ' , Γ ⊢ get[ i th-of n ] e :: (τs ⟦ i given i<∥τs∥ ⟧)
      TACtor : ∀{Δ Σ' Γ d cctx c e τ} →
                 (d , cctx) ∈ π1 Σ' →
                 (c , τ) ∈ cctx →
                 Δ , Σ' , Γ ⊢ e :: τ →
                 Δ , Σ' , Γ ⊢ C[ c ] e :: D[ d ]
      TACase : ∀{Δ Σ' Γ d cctx e rules τ} →
                 (d , cctx) ∈ π1 Σ' →
                 Δ , Σ' , Γ ⊢ e :: D[ d ] →
                 -- There must be a rule for each constructor, i.e. case exhuastiveness
                 (∀{c} → dom cctx c → dom rules c) →
                 (∀{c xc ec} →
                    (c , |C xc => ec) ∈ rules →
                      xc # Γ ∧
                      holes-disjoint ec e ∧
                      (∀{c' xc' ec'} → (c' , |C xc' => ec') ∈ rules → c ≠ c' → holes-disjoint ec ec') ∧
                      -- The constructor of each rule must be of the right datatype, and the branch must type-check
                      Σ[ τc ∈ typ ] (
                         (c , τc) ∈ cctx ∧
                         Δ , Σ' , (Γ ,, (xc , τc)) ⊢ ec :: τ)) →
                 Δ , Σ' , Γ ⊢ case e of⦃· rules ·⦄ :: τ
      -- TODO we may have a problem with weakening
      TAHole : ∀{Δ Σ' Γ u τ} → (u , (Γ , τ)) ∈ Δ → Δ , Σ' , Γ ⊢ ??[ u ] :: τ
      TAPF   : ∀{Δ Σ' Γ pf τ} → Σ' ⊢ PF pf :· τ → Δ , Σ' , Γ ⊢ PF pf :: τ
      TAAsrt : ∀{Δ Σ' Γ e1 e2 τ} →
                 holes-disjoint e1 e2 →
                 Δ , Σ' , Γ ⊢ e1 :: τ →
                 Δ , Σ' , Γ ⊢ e2 :: τ →
                 Δ , Σ' , Γ ⊢ PBE:assert e1 e2 :: ⟨ [] ⟩

    env : Set
    env = result ctx

    data _env-complete : env → Set where
      ENVC : ∀{E} → (∀{x rx} → (x , rx) ∈ E → rx rcomplete) → E env-complete

    data _env-final : env → Set where
      EF : ∀{E} → (∀{x rx} → (x , rx) ∈ E → rx final) → E env-final

    data _env-values : env → Set where
      EF : ∀{E} → (∀{x rx} → (x , rx) ∈ E → rx value) → E env-values

    -- results - evaluation takes expressions to results, but results aren't necessarily final
    data result : Set where
      [_]λ_=>_         : env → Nat → exp → result
      [_]fix_⦇·λ_=>_·⦈ : env → Nat → Nat → exp → result
      ⟨_⟩              : List result → result
      C[_]_            : Nat → result → result
      [_]??[_]         : env → Nat → result
      _∘_              : result → result → result
      get[_th-of_]_    : Nat → Nat → result → result
      [_]case_of⦃·_·⦄ : env → result → rule ctx → result
      PF              : pf → result

    -- values are final and complete (i.e. they have no holes)
    data _value : result → Set where
      VLam : ∀{E x e} → E env-values → e ecomplete → ([ E ]λ x => e) value
      VFix : ∀{E f x e} → E env-values → e ecomplete → [ E ]fix f ⦇·λ x => e ·⦈ value
      VTpl : ∀{rs} → (∀{i} → (h : i < ∥ rs ∥) → (rs ⟦ i given h ⟧) value) → ⟨ rs ⟩ value
      VCon : ∀{c r} → r value → (C[ c ] r) value
      VPF  : ∀{pf} → pf pf-value → (PF pf) value

    -- final results are those that cannot be evaluated further
    data _final : result → Set where
      FLam : ∀{E x e} → E env-final → ([ E ]λ x => e) final
      FFix : ∀{E f x e} → E env-final → [ E ]fix f ⦇·λ x => e ·⦈ final
      FTpl  : ∀{rs} → (∀{i} → (h : i < ∥ rs ∥) → (rs ⟦ i given h ⟧) final) → ⟨ rs ⟩ final
      FCon  : ∀{c r} → r final → (C[ c ] r) final
      FHole : ∀{E u} → E env-final → [ E ]??[ u ] final
      FAp   : ∀{r1 r2} → r1 final → r2 final → (∀{E x e} → r1 ≠ ([ E ]λ x => e)) → (∀{E f x e} → r1 ≠ [ E ]fix f ⦇·λ x => e ·⦈) → (r1 ∘ r2) final
      FGet  : ∀{i n r} → r final → (∀{rs} → r ≠ ⟨ rs ⟩) → (get[ i th-of n ] r) final
      FCase : ∀{E r rules} → r final → (∀{c r'} → r ≠ (C[ c ] r')) → E env-final → [ E ]case r of⦃· rules ·⦄ final
      FPF   : ∀{pf} → pf pf-final → (PF pf) final

    data _rcomplete : result → Set where
      RCLam  : ∀{E x e} → E env-complete → e ecomplete → ([ E ]λ x => e) rcomplete
      RCFix  : ∀{E f x e} → E env-complete → e ecomplete → [ E ]fix f ⦇·λ x => e ·⦈ rcomplete
      RCTpl  : ∀{rs} → (∀{i} → (i<∥rs∥ : i < ∥ rs ∥) → rs ⟦ i given i<∥rs∥ ⟧ rcomplete) → ⟨ rs ⟩ rcomplete
      RCCtor : ∀{c r} → r rcomplete → (C[ c ] r) rcomplete
      RCAp   : ∀{r1 r2} → r1 rcomplete → r2 rcomplete → (r1 ∘ r2) rcomplete
      RCGet  : ∀{i n r} → r rcomplete → (get[ i th-of n ] r) rcomplete
      RCCase : ∀{E r rules} →
                 E env-complete →
                 r rcomplete →
                 (∀{c rule} → (c , rule) ∈ rules → (rule.branch rule) ecomplete) →
                 [ E ]case r of⦃· rules ·⦄ rcomplete
      RCPF   : ∀{pf} → pf pf-complete → (PF pf) rcomplete

    data _,_,_⊢_ : hctx → denv → tctx → env → Set where
      EnvId  : ∀{Δ Σ'} → Δ , Σ' , ∅ ⊢ ∅
      EnvInd : ∀{Δ Σ' Γ E x τx rx} →
                 Δ , Σ' , Γ ⊢ E →
                 Δ , Σ' ⊢ rx ·: τx →
                 Δ , Σ' , (Γ ,, (x , τx)) ⊢ (E ,, (x , rx))

    -- type assignment for results
    data _,_⊢_·:_ : hctx → denv → result → typ → Set where
      TALam  : ∀{Δ Σ' Γ E x e τ} →
                 Δ , Σ' , Γ ⊢ E →
                 Δ , Σ' , Γ ⊢ ·λ x => e :: τ →
                 Δ , Σ' ⊢ [ E ]λ x => e ·: τ
      TAFix  : ∀{Δ Σ' Γ E f x e τ} →
                 Δ , Σ' , Γ ⊢ E →
                 Δ , Σ' , Γ ⊢ fix f ⦇·λ x => e ·⦈ :: τ →
                 Δ , Σ' ⊢ [ E ]fix f ⦇·λ x => e ·⦈ ·: τ
      TAApp  : ∀{Δ Σ' f arg τ1 τ2} →
                 Δ , Σ' ⊢ f ·: τ1 ==> τ2 →
                 Δ , Σ' ⊢ arg ·: τ1 →
                 Δ , Σ' ⊢ f ∘ arg ·: τ2
      TATpl  : ∀{Δ Σ' rs τs} →
                 ∥ rs ∥ == ∥ τs ∥ →
                 (∀{i} →
                    (i<∥rs∥ : i < ∥ rs ∥) →
                    (i<∥τs∥ : i < ∥ τs ∥) →
                    Δ , Σ' ⊢ rs ⟦ i given i<∥rs∥ ⟧ ·: (τs ⟦ i given i<∥τs∥ ⟧)) →
                 Δ , Σ' ⊢ ⟨ rs ⟩ ·: ⟨ τs ⟩
      TAGet  : ∀{Δ Σ' i r τs} →
                 (i<∥τs∥ : i < ∥ τs ∥) →
                 Δ , Σ' ⊢ r ·: ⟨ τs ⟩ →
                 Δ , Σ' ⊢ get[ i th-of ∥ τs ∥ ] r ·: (τs ⟦ i given i<∥τs∥ ⟧)
      TACtor : ∀{Δ Σ' d cctx c r τ} →
                 (d , cctx) ∈ π1 Σ' →
                 (c , τ) ∈ cctx →
                 Δ , Σ' ⊢ r ·: τ →
                 Δ , Σ' ⊢ C[ c ] r ·: D[ d ]
      TACase : ∀{Δ Σ' Γ E d cctx r rules τ} →
                 (d , cctx) ∈ π1 Σ' →
                 Δ , Σ' , Γ ⊢ E →
                 Δ , Σ' ⊢ r ·: D[ d ] →
                 -- There must be a rule for each constructor, i.e. case exhaustiveness
                 (∀{c} → dom cctx c → dom rules c) →
                 (∀{c xc ec} →
                    (c , |C xc => ec) ∈ rules →
                      xc # Γ ∧
                      -- The constructor of each rule must be of the right datatype, and the branch must type-check
                      Σ[ τc ∈ typ ] (
                         (c , τc) ∈ cctx ∧
                         Δ , Σ' , (Γ ,, (xc , τc)) ⊢ ec :: τ)) →
                 Δ , Σ' ⊢ [ E ]case r of⦃· rules ·⦄ ·: τ
      TAHole : ∀{Δ Σ' Γ E u τ} →
                 (u , (Γ , τ)) ∈ Δ →
                 Δ , Σ' , Γ ⊢ E →
                 Δ , Σ' ⊢ [ E ]??[ u ] ·: τ
      TAPF   : ∀{Δ Σ' pf τ} →
                 Σ' ⊢ PF pf :· τ →
                 Δ , Σ' ⊢ PF pf ·: τ

  world       = env ∧ ex
  worlds      = List world
  constraints = List (Nat ∧ world)

  data Constraints⦃_,_⦄:=_ : result → result → constraints → Set where
    XCEx     : ∀{E u pf} → Constraints⦃ [ E ]??[ u ] , PF pf ⦄:= ((u , E , PF pf) :: [])
    XCExSymm : ∀{E u pf} → Constraints⦃ PF pf , [ E ]??[ u ] ⦄:= ((u , E , PF pf) :: [])
    XCExRefl : ∀{r} → Constraints⦃ r , r ⦄:= []
    XCTpl    : ∀{rs1 rs2 ks} →
                 (_==_ {A = result} ⟨ rs1 ⟩ ⟨ rs2 ⟩ → ⊥) →
                 ∥ rs1 ∥ == ∥ rs2 ∥ →
                 ∥ rs1 ∥ == ∥ ks ∥ →
                 (∀{i} →
                    (i<∥rs1∥ : i < ∥ rs1 ∥) →
                    (i<∥rs2∥ : i < ∥ rs2 ∥) →
                    (i<∥ks∥ : i < ∥ ks ∥) →
                    Constraints⦃ rs1 ⟦ i given i<∥rs1∥ ⟧ , rs2 ⟦ i given i<∥rs2∥ ⟧ ⦄:= (ks ⟦ i given i<∥ks∥ ⟧)) →
                 Constraints⦃ ⟨ rs1 ⟩ , ⟨ rs2 ⟩ ⦄:= foldl _++_ [] ks
    XCCTor   : ∀{c r1 r2 k} →
                 (_==_ {A = result} (C[ c ] r1) (C[ c ] r2) → ⊥) →
                 Constraints⦃ r1 , r2 ⦄:= k →
                 Constraints⦃ C[ c ] r1 , C[ c ] r2 ⦄:= k
    XCAp     : ∀{rf1 rarg1 rf2 rarg2 kf karg} →
                 (_==_ {A = result} (rf1 ∘ rarg1) (rf2 ∘ rarg2) → ⊥) →
                 Constraints⦃ rf1 , rf2 ⦄:= kf →
                 Constraints⦃ rarg1 , rarg2 ⦄:= karg →
                 Constraints⦃ rf1 ∘ rarg1 , rf2 ∘ rarg2 ⦄:= kf ++ karg
    XCGet    : ∀{i n r1 r2 k} →
                 (_==_ {A = result} (get[ i th-of n ] r1) (get[ i th-of n ] r2) → ⊥) →
                 Constraints⦃ r1 , r2 ⦄:= k →
                 Constraints⦃ get[ i th-of n ] r1 , get[ i th-of n ] r2 ⦄:= k
    XCMatch  : ∀{E rules r1 r2 k} →
                 (_==_ {A = result} [ E ]case r1 of⦃· rules ·⦄ [ E ]case r2 of⦃· rules ·⦄ → ⊥) →
                 Constraints⦃ r1 , r2 ⦄:= k →
                 Constraints⦃ [ E ]case r1 of⦃· rules ·⦄ , [ E ]case r2 of⦃· rules ·⦄ ⦄:= k

  Constraints⦃_,_⦄:=∅ : result → result → Set
  Constraints⦃ r1 , r2 ⦄:=∅ = Σ[ k ∈ constraints ] Constraints⦃ r1 , r2 ⦄:= k → ⊥


  data Fuel : Set where
    ∞ : Fuel
    ⛽⟨_⟩ : Nat → Fuel

  data _⛽⇓_ : Fuel → Fuel → Set where
    CF∞ : ∞ ⛽⇓ ∞
    CF⛽ : ∀{n} → ⛽⟨ 1+ n ⟩ ⛽⇓ ⛽⟨ n ⟩

  -- Generic big step evaluation
  -- - If ⌊ ⛽ ⌋ is ∞, then there is no beta reduction limit,
  --   but the judgment will not go through unless evaluation eventually terminates.
  -- - If ⌊ ⛽ ⌋ is ⛽⟨ n ⟩, then the beta reduction limit is at most n,
  --   but if the limit is reached, the judgment will go through automatically.
  -- - Note that I'm using the term "beta reduction" a little loosely, as case
  --   evaluation also counts
  data _⊢_⌊_⌋⇒_⊣_ : env → exp → Fuel → result → constraints → Set where
    EFun             : ∀{E ⛽ x e} → E ⊢ ·λ x => e ⌊ ⛽ ⌋⇒ [ E ]λ x => e ⊣ []
    EFix             : ∀{E ⛽ f x e} → E ⊢ fix f ⦇·λ x => e ·⦈ ⌊ ⛽ ⌋⇒ [ E ]fix f ⦇·λ x => e ·⦈ ⊣ []
    EVar             : ∀{E ⛽ x r} → (x , r) ∈ E → E ⊢ X[ x ] ⌊ ⛽ ⌋⇒ r ⊣ []
    EHole            : ∀{E ⛽ u} → E ⊢ ??[ u ] ⌊ ⛽ ⌋⇒ [ E ]??[ u ] ⊣ []
    ETuple           : ∀{E ⛽ es rs ks} →
                         ∥ es ∥ == ∥ rs ∥ →
                         ∥ es ∥ == ∥ ks ∥ →
                         -- TODO this should probably factored out somehow
                         (∀{i} →
                            (i<∥es∥ : i < ∥ es ∥) →
                            (i<∥rs∥ : i < ∥ rs ∥) →
                            (i<∥ks∥ : i < ∥ ks ∥) →
                            E ⊢ es ⟦ i given i<∥es∥ ⟧ ⌊ ⛽ ⌋⇒ rs ⟦ i given i<∥rs∥ ⟧ ⊣ (ks ⟦ i given i<∥ks∥ ⟧)) →
                         E ⊢ ⟨ es ⟩ ⌊ ⛽ ⌋⇒ ⟨ rs ⟩ ⊣ foldl _++_ [] ks
    ECtor            : ∀{E ⛽ c e r k} →
                         E ⊢ e ⌊ ⛽ ⌋⇒ r ⊣ k →
                         E ⊢ C[ c ] e ⌊ ⛽ ⌋⇒ (C[ c ] r) ⊣ k
    EApp             : ∀{E ⛽ ⛽↓ e1 e2 Ef x ef kf r2 k2 r k} →
                         ⛽ ⛽⇓ ⛽↓ →
                         E ⊢ e1 ⌊ ⛽ ⌋⇒ ([ Ef ]λ x => ef) ⊣ kf →
                         E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ k2 →
                         (Ef ,, (x , r2)) ⊢ ef ⌊ ⛽↓ ⌋⇒ r ⊣ k →
                         E ⊢ e1 ∘ e2 ⌊ ⛽ ⌋⇒ r ⊣ kf ++ k2 ++ k
    EAppFix          : ∀{E ⛽ ⛽↓ e1 e2 Ef f x ef r1 k1 r2 k2 r k} →
                         ⛽ ⛽⇓ ⛽↓ →
                         r1 == [ Ef ]fix f ⦇·λ x => ef ·⦈ →
                         E ⊢ e1 ⌊ ⛽ ⌋⇒ r1 ⊣ k1 →
                         E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ k2 →
                         (Ef ,, (f , r1) ,, (x , r2)) ⊢ ef ⌊ ⛽↓ ⌋⇒ r ⊣ k →
                         E ⊢ e1 ∘ e2 ⌊ ⛽ ⌋⇒ r ⊣ k1 ++ k2 ++ k
    EAppUnfinished   : ∀{E ⛽ e1 e2 r1 k1 r2 k2} →
                         E ⊢ e1 ⌊ ⛽ ⌋⇒ r1 ⊣ k1 →
                         (∀{Ef x ef} → r1 ≠ ([ Ef ]λ x => ef)) →
                         (∀{Ef f x ef} → r1 ≠ [ Ef ]fix f ⦇·λ x => ef ·⦈) →
                         E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ k2 →
                         E ⊢ e1 ∘ e2 ⌊ ⛽ ⌋⇒ (r1 ∘ r2) ⊣ k1 ++ k2
    EGet             : ∀{E ⛽ i n e rs k} →
                         n == ∥ rs ∥ →
                         (h : i < ∥ rs ∥) →
                         E ⊢ e ⌊ ⛽ ⌋⇒ ⟨ rs ⟩ ⊣ k →
                         E ⊢ get[ i th-of n ] e ⌊ ⛽ ⌋⇒ (rs ⟦ i given h ⟧) ⊣ k
    EGetUnfinished   : ∀{E ⛽ i n e r k} →
                         E ⊢ e ⌊ ⛽ ⌋⇒ r ⊣ k →
                         (∀{rs} → r ≠ ⟨ rs ⟩) →
                         E ⊢ get[ i th-of n ] e ⌊ ⛽ ⌋⇒ (get[ i th-of n ] r) ⊣ k
    EMatch           : ∀{E ⛽ ⛽↓ e rules c xc ec r' k' r k} →
                         ⛽ ⛽⇓ ⛽↓ →
                         (c , |C xc => ec) ∈ rules →
                         E ⊢ e ⌊ ⛽ ⌋⇒ (C[ c ] r') ⊣ k' →
                         (E ,, (xc , r')) ⊢ ec ⌊ ⛽↓ ⌋⇒ r ⊣ k →
                         E ⊢ case e of⦃· rules ·⦄ ⌊ ⛽ ⌋⇒ r ⊣ k' ++ k
    EMatchUnfinished : ∀{E ⛽ e rules r k} →
                         E ⊢ e ⌊ ⛽ ⌋⇒ r ⊣ k →
                         (∀{c e'} → r ≠ (C[ c ] e')) →
                         E ⊢ case e of⦃· rules ·⦄ ⌊ ⛽ ⌋⇒ [ E ]case r of⦃· rules ·⦄ ⊣ k
    EPF              : ∀{E ⛽ pf} → (E ⊢ PF pf ⌊ ⛽ ⌋⇒ PF pf ⊣ [])
    EAsrt            : ∀{E ⛽ e1 r1 k1 e2 r2 k2 k3} →
                         E ⊢ e1 ⌊ ⛽ ⌋⇒ r1 ⊣ k1 →
                         E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ k2 →
                         Constraints⦃ r1 , r2 ⦄:= k3 →
                         E ⊢ PBE:assert e1 e2 ⌊ ⛽ ⌋⇒ ⟨ [] ⟩ ⊣ k1 ++ k2 ++ k3
    ELimit           : ∀{E e r} → E ⊢ e ⌊ ⛽⟨ 0 ⟩ ⌋⇒ r ⊣ []

  -- Big step evaluation - the ordinary variety with no beta reduction counting or limit
  _⊢_⇒_⊣_ : env → exp → result → constraints → Set
  E ⊢ e ⇒ r ⊣ k = E ⊢ e ⌊ ∞ ⌋⇒ r ⊣ k

  -- Generic constraint failure - this goes through if evaluation would fail due to unsatisfiable constraints,
  -- and it may go through if evaluation diverges. But it cannot be true if evaluation converges and all constraints are valid.
  data _⊢_⌊_⌋⇒∅ : env → exp → Fuel → Set where
    EFTpl        : ∀{E ⛽ es j} →
                     (j<∥es∥ : j < ∥ es ∥) →
                     E ⊢ es ⟦ j given j<∥es∥ ⟧ ⌊ ⛽ ⌋⇒∅ →
                     E ⊢ ⟨ es ⟩ ⌊ ⛽ ⌋⇒∅
    EFCtor       : ∀{E ⛽ c e} →
                     E ⊢ e ⌊ ⛽ ⌋⇒∅ →
                     E ⊢ C[ c ] e ⌊ ⛽ ⌋⇒∅
    EFAppFun     : ∀{E ⛽ e1 e2} →
                     E ⊢ e1 ⌊ ⛽ ⌋⇒∅ →
                     E ⊢ e1 ∘ e2 ⌊ ⛽ ⌋⇒∅
    EFAppArg     : ∀{E ⛽ e1 e2} →
                     E ⊢ e2 ⌊ ⛽ ⌋⇒∅ →
                     E ⊢ e1 ∘ e2 ⌊ ⛽ ⌋⇒∅
    EFAppEval    : ∀{E ⛽ ⛽↓ e1 Ef x ef k1 e2 r2 k2} →
                     ⛽ ⛽⇓ ⛽↓ →
                     E ⊢ e1 ⌊ ⛽ ⌋⇒ ([ Ef ]λ x => ef) ⊣ k1 →
                     E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ k2 →
                     (Ef ,, (x , r2)) ⊢ ef ⌊ ⛽↓ ⌋⇒∅ →
                     E ⊢ e1 ∘ e2 ⌊ ⛽ ⌋⇒∅
    EFAppFixEval : ∀{E ⛽ ⛽↓ e1 e2 Ef f x ef r1 k1 r2 k2} →
                     ⛽ ⛽⇓ ⛽↓ →
                     r1 == [ Ef ]fix f ⦇·λ x => ef ·⦈ →
                     E ⊢ e1 ⌊ ⛽ ⌋⇒ r1 ⊣ k1 →
                     E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ k2 →
                     (Ef ,, (f , r1) ,, (x , r2)) ⊢ ef ⌊ ⛽↓ ⌋⇒∅ →
                     E ⊢ e1 ∘ e2 ⌊ ⛽ ⌋⇒∅
    EFGet        : ∀{E ⛽ i n e} →
                     E ⊢ e ⌊ ⛽ ⌋⇒∅ →
                     E ⊢ get[ i th-of n ] e ⌊ ⛽ ⌋⇒∅
    EFMatchScrut : ∀{E ⛽ e rules} →
                     E ⊢ e ⌊ ⛽ ⌋⇒∅ →
                     E ⊢ case e of⦃· rules ·⦄ ⌊ ⛽ ⌋⇒∅
    EFMatchRule  : ∀{E ⛽ ⛽↓ e rules c xc ec r' k'} →
                     ⛽ ⛽⇓ ⛽↓ →
                     (c , |C xc => ec) ∈ rules →
                     E ⊢ e ⌊ ⛽ ⌋⇒ (C[ c ] r') ⊣ k' →
                     (E ,, (xc , r')) ⊢ ec ⌊ ⛽↓ ⌋⇒∅ →
                     E ⊢ case e of⦃· rules ·⦄ ⌊ ⛽ ⌋⇒∅
    EFAsrtL      : ∀{E ⛽ e1 e2} →
                     E ⊢ e1 ⌊ ⛽ ⌋⇒∅ →
                     E ⊢ PBE:assert e1 e2 ⌊ ⛽ ⌋⇒∅
    EFAsrtR      : ∀{E ⛽ e1 e2} →
                     E ⊢ e2 ⌊ ⛽ ⌋⇒∅ →
                     E ⊢ PBE:assert e1 e2 ⌊ ⛽ ⌋⇒∅
    EFAsrt       : ∀{E ⛽ e1 r1 k1 e2 r2 k2} →
                     E ⊢ e1 ⌊ ⛽ ⌋⇒ r1 ⊣ k1 →
                     E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ k2 →
                     Constraints⦃ r1 , r2 ⦄:=∅ →
                     E ⊢ PBE:assert e1 e2 ⌊ ⛽ ⌋⇒∅

  -- Constraint failure - the ordinary version with no beta reduction counting or limit
  _⊢_⇒∅ : env → exp → Set
  E ⊢ e ⇒∅ = E ⊢ e ⌊ ∞ ⌋⇒∅

  -- TODO we'll need some theorems for group
  -- TODO also theorems for everything below, including synthesis and solve
  group : constraints → worlds ctx
  group = list⇒ctx

  -- synthesis

  -- TODO proof that if _·⊨ v, then v value
  data _·⊨_ : ex → result → Set where
    SCtor : ∀{ex v c} →
              v value →
              ex ·⊨ v →
              (C[ c ] ex) ·⊨ (C[ c ] v)
    STpl  : ∀{exs vs} →
              ∥ exs ∥ == ∥ vs ∥ →
              (∀{i v} →
                 (i<∥exs∥ : i < ∥ exs ∥) →
                 (i<∥vs∥ : i < ∥ vs ∥) →
                 v == (vs ⟦ i given i<∥vs∥ ⟧) →
                   v value ∧
                   (exs ⟦ i given i<∥exs∥ ⟧) ·⊨ v) →
              ⟨ exs ⟩ ·⊨ ⟨ vs ⟩
    SPF   : ∀{E pf x e} →
              (∀{i v ex} →
                 (i<∥pf∥ : i < ∥ pf ∥) →
                 (v , ex) == pf ⟦ i given i<∥pf∥ ⟧ →
                 Σ[ v' ∈ result ] Σ[ k ∈ constraints ] (
                    (E ,, (x , v)) ⊢ e ⇒ v' ⊣ k ∧
                    v' value ∧
                    ex ·⊨ v')) →
              PF pf ·⊨ ([ E ]λ x => e)
    -- TODO SPFFix

  data _⊨_ : worlds → exp → Set where
    SEmpty : ∀{e} → [] ⊨ e
    SWorld : ∀{W E k ex v e} →
               W ⊨ e →
               E ⊢ e ⇒ v ⊣ k →
               v value →
               ex ·⊨ v →
               ((E , ex) :: W) ⊨ e

  mutual
    -- synthesis by refinement
    data _,_,_⊢_↑_ : denv → tctx → worlds → typ → exp → Set where
      IRCtor : ∀{Σ' Γ W W' d cctx c τ e} →
                 (d , cctx) ∈ π1 Σ' →
                 (c , τ) ∈ cctx →
                 W == map (λ {(E , ex) → (E , C[ c ] ex)}) W' →
                 Σ' , Γ , W' ⊢ τ ↑ e →
                 Σ' , Γ , W ⊢ D[ d ] ↑ (C[ c ] e)
      IRTpl : ∀{Σ' Γ n m W Es exs τs es} →
                n == ∥ es ∥ →
                n == ∥ τs ∥ →
                m == ∥ W ∥ →
                m == ∥ Es ∥ →
                m == ∥ exs ∥ →
                (∀{j} →
                   (j<∥exs∥ : j < ∥ exs ∥) →
                   n == ∥ exs ⟦ j given j<∥exs∥ ⟧ ∥) →
                (∀{j} →
                   (j<∥W∥ : j < ∥ W ∥) →
                   (j<∥Es∥ : j < ∥ Es ∥) →
                   (j<∥exs∥ : j < ∥ exs ∥) →
                   W ⟦ j given j<∥W∥ ⟧ == (Es ⟦ j given j<∥Es∥ ⟧ , ⟨ exs ⟦ j given j<∥exs∥ ⟧ ⟩)) →
                (∀{i} →
                   (i<∥τs∥ : i < ∥ τs ∥) →
                   (i<∥es∥ : i < ∥ es ∥) →
                   Σ[ Wi ∈ worlds ] (
                      (m == ∥ Wi ∥)
                        ∧
                      (∀{j} →
                         (j<∥Wi∥ : j < ∥ Wi ∥) →
                         (j<∥Es∥ : j < ∥ Es ∥) →
                         (j<∥exs∥ : j < ∥ exs ∥) →
                         (i<∥exsj∥ : i < ∥ exs ⟦ j given j<∥exs∥ ⟧ ∥) →
                         Wi ⟦ j given j<∥Wi∥ ⟧ == (Es ⟦ j given j<∥Es∥ ⟧ , exs ⟦ j given j<∥exs∥ ⟧ ⟦ i given i<∥exsj∥ ⟧))
                        ∧
                      (Σ' , Γ , Wi ⊢ τs ⟦ i given i<∥τs∥ ⟧ ↑ (es ⟦ i given i<∥es∥ ⟧)))) →
                Σ' , Γ , W ⊢ ⟨ τs ⟩ ↑ ⟨ es ⟩
      IRLam : ∀{Σ' Γ W W' τ1 τ2 ⦇E,pf⦈s x e} →
                ∥ ⦇E,pf⦈s ∥ == ∥ W ∥ →
                -- Each example in the worlds is a partial function
                -- The envs and pfs are destructed and retained in ⦇E,pf⦈s
                (∀{i} →
                   (i<∥W∥ : i < ∥ W ∥) →
                   (i<∥Epfs∥ : i < ∥ ⦇E,pf⦈s ∥) →
                   Σ[ E ∈ env ] Σ[ pf ∈ pf ] (
                      (E , PF pf) == W ⟦ i given i<∥W∥ ⟧ ∧
                      (E , pf) == ⦇E,pf⦈s ⟦ i given i<∥Epfs∥ ⟧)) →
                W' == concat
                        (map (λ {(E , pf) →
                           map (λ {(v , ex) →
                             ((E ,, (x , v)) , ex)})
                             pf})
                           ⦇E,pf⦈s) →
                Σ' , (Γ ,, (x , τ1)) , W' ⊢ τ2 ↑ e →
                Σ' , Γ , W ⊢ τ1 ==> τ2 ↑ (·λ x => e)
      -- TODO IRFix
      IRMatch : ∀{Σ' Γ W W' W'' τ e rules d cctx x} →
                  -- choose a datatype
                  (d , cctx) ∈ π1 Σ' →
                  -- choose one fresh variable name that will be used for all cases
                  x # Γ →
                  -- synthesize a scrutinee
                  Σ' , Γ ⊢ D[ d ] ↥ e →
                  (∀{c rule} →
                     (c , rule) ∈ rules →
                     dom cctx c ∧ rule.parm rule == x) →
                  ∥ W' ∥ == ∥ W ∥ →
                  -- W' contains the same worlds as W, but each one is packaged with
                  -- the constructor name and value that the scrutinee would evaluate
                  -- to in that world.
                  (∀{i E ex} →
                     (i<∥W∥ : i < ∥ W ∥) →
                     (i<∥W'∥ : i < ∥ W' ∥) →
                     (E , ex) == W ⟦ i given i<∥W∥ ⟧ →
                     Σ[ c ∈ Nat ] Σ[ v ∈ result ] (
                       dom cctx c ∧
                       v value ∧
                       (c , E , ex , v) == W' ⟦ i given i<∥W'∥ ⟧ ∧
                       E ⊢ e ⇒ C[ c ] v ⊣ [])) →
                  -- For each c in the domain of cctx, W'' maps to a list of extended worlds,
                  -- where each extended world has the specified example, but an env where the
                  -- branch variable x is assosiated with the value that the scrutinee evaluates
                  -- to under the original env.
                  W'' ==
                    (ctxmap (λ _ → []) cctx)
                      ∪
                    ctxmap (map λ {(E , ex , v) → (E ,, (x , v)) , ex}) (list⇒ctx W') →
                  -- Each rule's branch expression must synthesize under the aforementioned
                  -- extended worlds.
                  (∀{c τc} →
                     (c , τc) ∈ cctx →
                     Σ[ ec ∈ exp ] Σ[ Wc ∈ worlds ] (
                        (c , Wc) ∈ W'' ∧
                        (c , |C x => ec) ∈ rules ∧
                        Σ' , (Γ ,, (x , τc)) , Wc ⊢ τ ↑ ec)) →
                  Σ' , Γ , W ⊢ τ ↑ case e of⦃· rules ·⦄
      IRGuess : ∀{Σ' Γ W τ e} →
                  Σ' , Γ ⊢ τ ↥ e →
                  W ⊨ e →
                  Σ' , Γ , W ⊢ τ ↑ e

    -- synthesis by guess
    data _,_⊢_↥_ : denv → tctx → typ → exp → Set where
      EGVar : ∀{Σ' Γ τ x} →
                (x , τ) ∈ Γ →
                Σ' , Γ ⊢ τ ↥ X[ x ]
      EGApp : ∀{Σ' Γ τ1 τ2 e1 e2} →
                Σ' , Γ ⊢ τ1 ==> τ2 ↥ e1 →
                Σ' , Γ , [] ⊢ τ1 ↑ e2 →
                Σ' , Γ ⊢ τ2 ↥ (e1 ∘ e2)
      EGGet : ∀{Σ' Γ τs i n e} →
                n == ∥ τs ∥ →
                (i<∥τs∥ : i < ∥ τs ∥) →
                Σ' , Γ ⊢ ⟨ τs ⟩ ↥ e →
                Σ' , Γ ⊢ τs ⟦ i given i<∥τs∥ ⟧ ↥ (get[ i th-of n ] e)

  data _,_⊢Solve_:=_ : hctx → denv → constraints → exp ctx → Set where
    Sol : ∀{Δ Σ' k g s} →
            g == group k →
            (∀{u} → dom g u → dom Δ u) →
            (∀{u} → dom g u → dom s u) →
            (∀{u} → dom s u → dom g u) →
            (∀{u Wu Γu τu su} →
               (u , Wu) ∈ g →
               (u , Γu , τu) ∈ Δ →
               (u , su) ∈ s →
               Σ' , Γu , Wu ⊢ τu ↑ su) →
            Δ , Σ' ⊢Solve k := s

{- TODO

  -- those external expressions without holes
  data _ecomplete : hexp → Set where
    ECConst : c ecomplete
    ECAsc : ∀{τ e} → τ tcomplete → e ecomplete → (e ·: τ) ecomplete
    ECVar : ∀{x} → (X x) ecomplete
    ECLam1 : ∀{x e} → e ecomplete → (·λ x e) ecomplete
    ECLam2 : ∀{x e τ} → e ecomplete → τ tcomplete → (·λ x [ τ ] e) ecomplete
    ECAp : ∀{e1 e2} → e1 ecomplete → e2 ecomplete → (e1 ∘ e2) ecomplete
    ECFst : ∀{e} → e ecomplete → (fst e) ecomplete
    ECSnd : ∀{e} → e ecomplete → (snd e) ecomplete
    ECPair : ∀{e1 e2} → e1 ecomplete → e2 ecomplete → ⟨ e1 , e2 ⟩ ecomplete

  -- those internal expressions without holes
  data _dcomplete : ihexp → Set where
    DCVar : ∀{x} → (X x) dcomplete
    DCConst : c dcomplete
    DCLam : ∀{x τ d} → d dcomplete → τ tcomplete → (·λ x [ τ ] d) dcomplete
    DCAp : ∀{d1 d2} → d1 dcomplete → d2 dcomplete → (d1 ∘ d2) dcomplete
    DCCast : ∀{d τ1 τ2} → d dcomplete → τ1 tcomplete → τ2 tcomplete → (d ⟨ τ1 ⇒ τ2 ⟩) dcomplete
    DCFst : ∀{d} → d dcomplete → (fst d) dcomplete
    DCSnd : ∀{d} → d dcomplete → (snd d) dcomplete
    DCPair : ∀{d1 d2} → d1 dcomplete → d2 dcomplete → ⟨ d1 , d2 ⟩ dcomplete

  mutual
    -- substitution typing
    data _,_⊢_:s:_ : hctx → tctx → env → tctx → Set where
      STAId : ∀{Γ Γ' Δ} →
                  ((x : Nat) (τ : htyp) → (x , τ) ∈ Γ' → (x , τ) ∈ Γ) →
                  Δ , Γ ⊢ Id Γ' :s: Γ'
      STASubst : ∀{Γ Δ σ y Γ' d τ } →
               Δ , Γ ,, (y , τ) ⊢ σ :s: Γ' →
               Δ , Γ ⊢ d :: τ →
               Δ , Γ ⊢ Subst d y σ :s: Γ'

    -- type assignment
    data _,_⊢_::_ : (Δ : hctx) (Γ : tctx) (d : ihexp) (τ : htyp) → Set where
      TAConst : ∀{Δ Γ} → Δ , Γ ⊢ c :: b
      TAVar : ∀{Δ Γ x τ} → (x , τ) ∈ Γ → Δ , Γ ⊢ X x :: τ
      TALam : ∀{ Δ Γ x τ1 d τ2} →
              x # Γ →
              Δ , (Γ ,, (x , τ1)) ⊢ d :: τ2 →
              Δ , Γ ⊢ ·λ x [ τ1 ] d :: (τ1 ==> τ2)
      TAAp : ∀{ Δ Γ d1 d2 τ1 τ} →
             Δ , Γ ⊢ d1 :: τ1 ==> τ →
             Δ , Γ ⊢ d2 :: τ1 →
             Δ , Γ ⊢ d1 ∘ d2 :: τ
      TAEHole : ∀{ Δ Γ σ u Γ' τ} →
                (u , (Γ' , τ)) ∈ Δ →
                Δ , Γ ⊢ σ :s: Γ' →
                Δ , Γ ⊢ ⦇⦈⟨ u , σ ⟩ :: τ
      TANEHole : ∀ { Δ Γ d τ' Γ' u σ τ } →
                 (u , (Γ' , τ)) ∈ Δ →
                 Δ , Γ ⊢ d :: τ' →
                 Δ , Γ ⊢ σ :s: Γ' →
                 Δ , Γ ⊢ ⦇⌜ d ⌟⦈⟨ u , σ ⟩ :: τ
      TACast : ∀{ Δ Γ d τ1 τ2} →
             Δ , Γ ⊢ d :: τ1 →
             τ1 ~ τ2 →
             Δ , Γ ⊢ d ⟨ τ1 ⇒ τ2 ⟩ :: τ2
      TAFailedCast : ∀{Δ Γ d τ1 τ2} →
             Δ , Γ ⊢ d :: τ1 →
             τ1 ground →
             τ2 ground →
             τ1 ≠ τ2 →
             Δ , Γ ⊢ d ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩ :: τ2
      TAFst : ∀{Δ Γ d τ1 τ2} →
             Δ , Γ ⊢ d :: τ1 ⊗ τ2 →
             Δ , Γ ⊢ fst d :: τ1
      TASnd : ∀{Δ Γ d τ1 τ2} →
             Δ , Γ ⊢ d :: τ1 ⊗ τ2 →
             Δ , Γ ⊢ snd d :: τ2
      TAPair : ∀{Δ Γ d1 d2 τ1 τ2} →
             Δ , Γ ⊢ d1 :: τ1 →
             Δ , Γ ⊢ d2 :: τ2 →
             Δ , Γ ⊢ ⟨ d1 , d2 ⟩ :: τ1 ⊗ τ2

  -- substitution
  [_/_]_ : ihexp → Nat → ihexp → ihexp
  [ d / y ] c = c
  [ d / y ] X x
    with natEQ x y
  [ d / y ] X .y | Inl refl = d
  [ d / y ] X x  | Inr neq = X x
  [ d / y ] (·λ x [ x₁ ] d')
    with natEQ x y
  [ d / y ] (·λ .y [ τ ] d') | Inl refl = ·λ y [ τ ] d'
  [ d / y ] (·λ x [ τ ] d')  | Inr x₁ = ·λ x [ τ ] ( [ d / y ] d')
  [ d / y ] ⦇⦈⟨ u , σ ⟩ = ⦇⦈⟨ u , Subst d y σ ⟩
  [ d / y ] ⦇⌜ d' ⌟⦈⟨ u , σ  ⟩ =  ⦇⌜ [ d / y ] d' ⌟⦈⟨ u , Subst d y σ ⟩
  [ d / y ] (d1 ∘ d2) = ([ d / y ] d1) ∘ ([ d / y ] d2)
  [ d / y ] (d' ⟨ τ1 ⇒ τ2 ⟩ ) = ([ d / y ] d') ⟨ τ1 ⇒ τ2 ⟩
  [ d / y ] (d' ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩ ) = ([ d / y ] d') ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩
  [ d / y ] ⟨ d1 , d2 ⟩ = ⟨ [ d / y ] d1 , [ d / y ] d2 ⟩
  [ d / y ] (fst d') = fst ([ d / y ] d')
  [ d / y ] (snd d') = snd ([ d / y ] d')

  -- applying an environment to an expression
  apply-env : env → ihexp → ihexp
  apply-env (Id Γ) d = d
  apply-env (Subst d y σ) d' = [ d / y ] ( apply-env σ d')

  -- freshness
  mutual
    -- ... with respect to a hole context
    data envfresh : Nat → env → Set where
      EFId : ∀{x Γ} → x # Γ → envfresh x (Id Γ)
      EFSubst : ∀{x d σ y} → fresh x d
                           → envfresh x σ
                           → x ≠ y
                           → envfresh x (Subst d y σ)

    -- ... for inernal expressions
    data fresh : Nat → ihexp → Set where
      FConst : ∀{x} → fresh x c
      FVar   : ∀{x y} → x ≠ y → fresh x (X y)
      FLam   : ∀{x y τ d} → x ≠ y → fresh x d → fresh x (·λ y [ τ ] d)
      FHole  : ∀{x u σ} → envfresh x σ → fresh x (⦇⦈⟨ u , σ ⟩)
      FNEHole : ∀{x d u σ} → envfresh x σ → fresh x d → fresh x (⦇⌜ d ⌟⦈⟨ u , σ ⟩)
      FAp     : ∀{x d1 d2} → fresh x d1 → fresh x d2 → fresh x (d1 ∘ d2)
      FCast   : ∀{x d τ1 τ2} → fresh x d → fresh x (d ⟨ τ1 ⇒ τ2 ⟩)
      FFailedCast : ∀{x d τ1 τ2} → fresh x d → fresh x (d ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩)
      FFst  : ∀{x d} → fresh x d → fresh x (fst d)
      FSnd  : ∀{x d} → fresh x d → fresh x (snd d)
      FPair : ∀{x d1 d2} → fresh x d1 → fresh x d2 → fresh x ⟨ d1 , d2 ⟩

  -- ... for external expressions
  data freshh : Nat → hexp → Set where
    FRHConst : ∀{x} → freshh x c
    FRHAsc   : ∀{x e τ} → freshh x e → freshh x (e ·: τ)
    FRHVar   : ∀{x y} → x ≠ y → freshh x (X y)
    FRHLam1  : ∀{x y e} → x ≠ y → freshh x e → freshh x (·λ y e)
    FRHLam2  : ∀{x τ e y} → x ≠ y → freshh x e → freshh x (·λ y [ τ ] e)
    FRHEHole : ∀{x u} → freshh x (⦇⦈[ u ])
    FRHNEHole : ∀{x u e} → freshh x e → freshh x (⦇⌜ e ⌟⦈[ u ])
    FRHAp : ∀{x e1 e2} → freshh x e1 → freshh x e2 → freshh x (e1 ∘ e2)
    FRHFst  : ∀{x e} → freshh x e → freshh x (fst e)
    FRHSnd  : ∀{x e} → freshh x e → freshh x (snd e)
    FRHPair : ∀{x e1 e2} → freshh x e1 → freshh x e2 → freshh x ⟨ e1 , e2 ⟩

  -- with respect to all bindings in a context
  freshΓ : {A : Set} → (Γ : A ctx) → (e : hexp) → Set
  freshΓ {A} Γ e = (x : Nat) → dom Γ x → freshh x e

  -- x is not used in a binding site in d
  mutual
    data unbound-in-σ : Nat → env → Set where
      UBσId : ∀{x Γ} → unbound-in-σ x (Id Γ)
      UBσSubst : ∀{x d y σ} → unbound-in x d
                            → unbound-in-σ x σ
                            → x ≠ y
                            → unbound-in-σ x (Subst d y σ)

    data unbound-in : (x : Nat) (d : ihexp) → Set where
      UBConst : ∀{x} → unbound-in x c
      UBVar : ∀{x y} → unbound-in x (X y)
      UBLam2 : ∀{x d y τ} → x ≠ y
                           → unbound-in x d
                           → unbound-in x (·λ_[_]_ y τ d)
      UBHole : ∀{x u σ} → unbound-in-σ x σ
                         → unbound-in x (⦇⦈⟨ u , σ ⟩)
      UBNEHole : ∀{x u σ d }
                  → unbound-in-σ x σ
                  → unbound-in x d
                  → unbound-in x (⦇⌜ d ⌟⦈⟨ u , σ ⟩)
      UBAp : ∀{ x d1 d2 } →
            unbound-in x d1 →
            unbound-in x d2 →
            unbound-in x (d1 ∘ d2)
      UBCast : ∀{x d τ1 τ2} → unbound-in x d → unbound-in x (d ⟨ τ1 ⇒ τ2 ⟩)
      UBFailedCast : ∀{x d τ1 τ2} → unbound-in x d → unbound-in x (d ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩)
      UBFst  : ∀{x d} → unbound-in x d → unbound-in x (fst d)
      UBSnd  : ∀{x d} → unbound-in x d → unbound-in x (snd d)
      UBPair : ∀{x d1 d2} → unbound-in x d1 → unbound-in x d2 → unbound-in x ⟨ d1 , d2 ⟩

  mutual
    data binders-disjoint-σ : env → ihexp → Set where
      BDσId : ∀{Γ d} → binders-disjoint-σ (Id Γ) d
      BDσSubst : ∀{d1 d2 y σ} → binders-disjoint d1 d2
                              → binders-disjoint-σ σ d2
                              → binders-disjoint-σ (Subst d1 y σ) d2

    -- two terms that do not share any binders
    data binders-disjoint : (d1 : ihexp) → (d2 : ihexp) → Set where
      BDConst : ∀{d} → binders-disjoint c d
      BDVar : ∀{x d} → binders-disjoint (X x) d
      BDLam : ∀{x τ d1 d2} → binders-disjoint d1 d2
                            → unbound-in x d2
                            → binders-disjoint (·λ_[_]_ x τ d1) d2
      BDHole : ∀{u σ d2} → binders-disjoint-σ σ d2
                         → binders-disjoint (⦇⦈⟨ u , σ ⟩) d2
      BDNEHole : ∀{u σ d1 d2} → binders-disjoint-σ σ d2
                              → binders-disjoint d1 d2
                              → binders-disjoint (⦇⌜ d1 ⌟⦈⟨ u , σ ⟩) d2
      BDAp :  ∀{d1 d2 d3} → binders-disjoint d1 d3
                          → binders-disjoint d2 d3
                          → binders-disjoint (d1 ∘ d2) d3
      BDCast : ∀{d1 d2 τ1 τ2} → binders-disjoint d1 d2 → binders-disjoint (d1 ⟨ τ1 ⇒ τ2 ⟩) d2
      BDFailedCast : ∀{d1 d2 τ1 τ2} → binders-disjoint d1 d2 → binders-disjoint (d1 ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩) d2
      BDFst  : ∀{d1 d2} → binders-disjoint d1 d2 → binders-disjoint (fst d1) d2
      BDSnd  : ∀{d1 d2} → binders-disjoint d1 d2 → binders-disjoint (snd d1) d2
      BDPair : ∀{d1 d2 d3} →
               binders-disjoint d1 d3 →
               binders-disjoint d2 d3 →
               binders-disjoint ⟨ d1 , d2 ⟩ d3

  mutual
  -- each term has to be binders unique, and they have to be pairwise
  -- disjoint with the collection of bound vars
    data binders-unique-σ : env → Set where
      BUσId : ∀{Γ} → binders-unique-σ (Id Γ)
      BUσSubst : ∀{d y σ} → binders-unique d
                          → binders-unique-σ σ
                          → binders-disjoint-σ σ d
                          → binders-unique-σ (Subst d y σ)

    -- all the variable names in the term are unique
    data binders-unique : ihexp → Set where
      BUHole : binders-unique c
      BUVar : ∀{x} → binders-unique (X x)
      BULam : {x : Nat} {τ : htyp} {d : ihexp} → binders-unique d
                                                → unbound-in x d
                                                → binders-unique (·λ_[_]_ x τ d)
      BUEHole : ∀{u σ} → binders-unique-σ σ
                        → binders-unique (⦇⦈⟨ u , σ ⟩)
      BUNEHole : ∀{u σ d} → binders-unique d
                           → binders-unique-σ σ
                           → binders-unique (⦇⌜ d ⌟⦈⟨ u , σ ⟩)
      BUAp : ∀{d1 d2} → binders-unique d1
                       → binders-unique d2
                       → binders-disjoint d1 d2
                       → binders-unique (d1 ∘ d2)
      BUCast : ∀{d τ1 τ2} → binders-unique d
                           → binders-unique (d ⟨ τ1 ⇒ τ2 ⟩)
      BUFailedCast : ∀{d τ1 τ2} → binders-unique d
                                 → binders-unique (d ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩)
      BUFst  : ∀{d} →
               binders-unique d →
               binders-unique (fst d)
      BUSnd  : ∀{d} →
               binders-unique d →
               binders-unique (snd d)
      BUPair : ∀{d1 d2} →
               binders-unique d1 →
               binders-unique d2 →
               binders-disjoint d1 d2 →
               binders-unique ⟨ d1 , d2 ⟩

-}
