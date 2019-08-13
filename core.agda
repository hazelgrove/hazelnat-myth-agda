open import Nat
open import Prelude
open import List
open import contexts

module core where
  -- types
  data typ : Set where
    _==>_ : typ → typ → typ
    ⟨⟩    : typ
    ⟨_×_⟩ : typ → typ → typ
    D[_]  : Nat → typ

  -- arrow type constructors bind very tightly
  infixr 25  _==>_

  tctx = typ ctx
  -- TODO we should restrict this to exclude arrow types
  hctx = (tctx ∧ typ) ctx
  denv = Σ[ dctx ∈ tctx ctx ]
    ∀{d1 d2 cctx1 cctx2 c} →
    d1 ≠ d2 →
    (d1 , cctx1) ∈ dctx →
    (d2 , cctx2) ∈ dctx →
    c # cctx1 ∨ c # cctx2

  -- simple values
  data val : Set where
    ⟨⟩    : val
    ⟨_,_⟩ : val → val → val
    C[_]_ : Nat → val → val

  -- examples
  data ex : Set where
    ⟨⟩    : ex
    ⟨_,_⟩ : ex → ex → ex
    C[_]_ : Nat → ex → ex
    _↦_  : val → ex → ex
    ¿¿    : ex

  -- simple value typing
  data _⊢_::ⱽ_ : denv → val → typ → Set where
    TSVUnit : ∀{Σ'} → Σ' ⊢ ⟨⟩ ::ⱽ ⟨⟩
    TSVPair : ∀{Σ' v1 v2 τ1 τ2} →
                Σ' ⊢ v1 ::ⱽ τ1 →
                Σ' ⊢ v2 ::ⱽ τ2 →
                Σ' ⊢ ⟨ v1 , v2 ⟩ ::ⱽ ⟨ τ1 × τ2 ⟩
    TSVCtor : ∀{Σ' d cctx c v τ} →
                (d , cctx) ∈ π1 Σ' →
                (c , τ) ∈ cctx →
                Σ' ⊢ v ::ⱽ τ →
                Σ' ⊢ C[ c ] v ::ⱽ D[ d ]

  -- example typing
  data _,_⊢_:·_ : hctx → denv → ex → typ → Set where
    TAUnit : ∀{Δ Σ'} → Δ , Σ' ⊢ ⟨⟩ :· ⟨⟩
    TAPair : ∀{Δ Σ' ex1 ex2 τ1 τ2} →
               Δ , Σ' ⊢ ex1 :· τ1 →
               Δ , Σ' ⊢ ex2 :· τ2 →
               Δ , Σ' ⊢ ⟨ ex1 , ex2 ⟩ :· ⟨ τ1 × τ2 ⟩
    TACtor : ∀{Δ Σ' d cctx c ex τ} →
               (d , cctx) ∈ π1 Σ' →
               (c , τ) ∈ cctx →
               Δ , Σ' ⊢ ex :· τ →
               Δ , Σ' ⊢ C[ c ] ex :· D[ d ]
    TADC   : ∀{Δ Σ' τ} → Δ , Σ' ⊢ ¿¿ :· τ
    TAMap  : ∀{Δ Σ' v ex τ1 τ2} →
               Σ' ⊢ v ::ⱽ τ1 →
               Δ , Σ' ⊢ ex :· τ2 →
               Δ , Σ' ⊢ v ↦ ex :· τ1 ==> τ2

  mutual
    record rule : Set where
      inductive
      constructor |C_=>_
      field
        parm   : Nat
        branch : exp

    -- Expressions (Sketches)
    data exp : Set where
      fix_⦇·λ_=>_·⦈ : Nat → Nat → exp → exp
      X[_]          : Nat → exp
      _∘_           : exp → exp → exp
      ⟨⟩            : exp
      ⟨_,_⟩         : exp → exp → exp
      fst           : exp → exp
      snd           : exp → exp
      C[_]_         : Nat → exp → exp
      case_of⦃·_·⦄ : exp → rule ctx → exp
      ??[_]         : Nat → exp
      PBE:assert    : exp → exp → exp

  data hole-name-new : (e : exp) → (u : Nat) → Set where
    HNNFix  : ∀{x f e u} → hole-name-new e u → hole-name-new (fix f ⦇·λ x => e ·⦈) u
    HNNVar  : ∀{x u} → hole-name-new (X[ x ]) u
    HNNAp   : ∀{e1 e2 u} → hole-name-new e1 u → hole-name-new e2 u → hole-name-new (e1 ∘ e2) u
    HNNUnit : ∀{u} → hole-name-new ⟨⟩ u
    HNNPair : ∀{e1 e2 u} → hole-name-new e1 u → hole-name-new e2 u → hole-name-new ⟨ e1 , e2 ⟩ u
    HNNFst  : ∀{e u} → hole-name-new e u → hole-name-new (fst e) u
    HNNSnd  : ∀{e u} → hole-name-new e u → hole-name-new (snd e) u
    HNNCtor : ∀{c e u} → hole-name-new e u → hole-name-new (C[ c ] e) u
    HNNCase : ∀{e rules u} →
                hole-name-new e u →
                (∀{c rule} → (c , rule) ∈ rules → hole-name-new (rule.branch rule) u) →
                hole-name-new (case e of⦃· rules ·⦄) u
    HNNHole : ∀{u' u} → u' ≠ u → hole-name-new (??[ u' ]) u
    HNNAsrt : ∀{e1 e2 u} → hole-name-new e1 u → hole-name-new e2 u → hole-name-new (PBE:assert e1 e2) u

  data holes-disjoint : (e1 : exp) → (e2 : exp) → Set where
    HDFix  : ∀{x f e e'} → holes-disjoint e e' → holes-disjoint (fix f ⦇·λ x => e ·⦈) e'
    HDVar  : ∀{x e'} → holes-disjoint (X[ x ]) e'
    HDAp   : ∀{e1 e2 e'} → holes-disjoint e1 e' → holes-disjoint e2 e' → holes-disjoint (e1 ∘ e2) e'
    HDUnit : ∀{e'} → holes-disjoint ⟨⟩ e'
    HDPair : ∀{e1 e2 e'} → holes-disjoint e1 e' → holes-disjoint e2 e' → holes-disjoint ⟨ e1 , e2 ⟩ e'
    HDFst  : ∀{e e'} → holes-disjoint e e' → holes-disjoint (fst e) e'
    HDSnd  : ∀{e e'} → holes-disjoint e e' → holes-disjoint (snd e) e'
    HDCtor : ∀{c e e'} → holes-disjoint e e' → holes-disjoint (C[ c ] e) e'
    HDCase : ∀{e rules e'} →
               holes-disjoint e e' →
               (∀{c rule} → (c , rule) ∈ rules → holes-disjoint (rule.branch rule) e') →
               holes-disjoint (case e of⦃· rules ·⦄) e'
    HDHole : ∀{u e'} → hole-name-new e' u → holes-disjoint (??[ u ]) e'
    HDAsrt : ∀{e1 e2 e'} → holes-disjoint e1 e' → holes-disjoint e2 e' → holes-disjoint (PBE:assert e1 e2) e'

  data _ecomplete : exp → Set where
    ECFix  : ∀{f x e} → e ecomplete → fix f ⦇·λ x => e ·⦈ ecomplete
    ECVar  : ∀{x} → X[ x ] ecomplete
    ECAp   : ∀{e1 e2} → e1 ecomplete → e2 ecomplete → (e1 ∘ e2) ecomplete
    ECUnit : ⟨⟩ ecomplete
    ECPair : ∀{e1 e2} → e1 ecomplete → e2 ecomplete → ⟨ e1 , e2 ⟩ ecomplete
    ECFst  : ∀{e} → e ecomplete → (fst e) ecomplete
    ECSnd  : ∀{e} → e ecomplete → (snd e) ecomplete
    ECCtor : ∀{c e} → e ecomplete → (C[ c ] e) ecomplete
    ECCase : ∀{e rules} →
               e ecomplete →
               (∀{c rule} → (c , rule) ∈ rules → (rule.branch rule) ecomplete) →
               case e of⦃· rules ·⦄ ecomplete
    ECAsrt : ∀{e1 e2} → e1 ecomplete → e2 ecomplete → (PBE:assert e1 e2) ecomplete

  -- type assignment for expressions
  data _,_,_⊢_::_ : hctx → denv → tctx → exp → typ → Set where
    TAFix  : ∀{Δ Σ' Γ f x e τ1 τ2} →
               Δ , Σ' , (Γ ,, (f , τ1 ==> τ2) ,, (x , τ1)) ⊢ e :: τ2 →
               Δ , Σ' , Γ ⊢ fix f ⦇·λ x => e ·⦈ :: τ1 ==> τ2
    TAVar  : ∀{Δ Σ' Γ x τ} → (x , τ) ∈ Γ → Δ , Σ' , Γ ⊢ X[ x ] :: τ
    TAApp  : ∀{Δ Σ' Γ f arg τ1 τ2} →
               holes-disjoint f arg →
               Δ , Σ' , Γ ⊢ f :: τ1 ==> τ2 →
               Δ , Σ' , Γ ⊢ arg :: τ1 →
               Δ , Σ' , Γ ⊢ f ∘ arg :: τ2
    TAUnit : ∀{Δ Σ' Γ} → Δ , Σ' , Γ ⊢ ⟨⟩ :: ⟨⟩
    TAPair : ∀{Δ Σ' Γ e1 e2 τ1 τ2} →
               holes-disjoint e1 e2 →
               Δ , Σ' , Γ ⊢ e1 :: τ1 →
               Δ , Σ' , Γ ⊢ e2 :: τ2 →
               Δ , Σ' , Γ ⊢ ⟨ e1 , e2 ⟩ :: ⟨ τ1 × τ2 ⟩
    TAFst  : ∀{Δ Σ' Γ e τ1 τ2} →
               Δ , Σ' , Γ ⊢ e :: ⟨ τ1 × τ2 ⟩ →
               Δ , Σ' , Γ ⊢ fst e :: τ1
    TASnd  : ∀{Δ Σ' Γ e τ1 τ2} →
               Δ , Σ' , Γ ⊢ e :: ⟨ τ1 × τ2 ⟩ →
               Δ , Σ' , Γ ⊢ snd e :: τ2
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
                    holes-disjoint ec e ∧
                    (∀{c' xc' ec'} → (c' , |C xc' => ec') ∈ rules → c ≠ c' → holes-disjoint ec ec') ∧
                    -- The constructor of each rule must be of the right datatype, and the branch must type-check
                    Σ[ τc ∈ typ ] (
                       (c , τc) ∈ cctx ∧
                       Δ , Σ' , (Γ ,, (xc , τc)) ⊢ ec :: τ)) →
               Δ , Σ' , Γ ⊢ case e of⦃· rules ·⦄ :: τ
    TAHole : ∀{Δ Σ' Γ u τ} → (u , (Γ , τ)) ∈ Δ → Δ , Σ' , Γ ⊢ ??[ u ] :: τ
    TAAsrt : ∀{Δ Σ' Γ e1 e2 τ} →
               holes-disjoint e1 e2 →
               Δ , Σ' , Γ ⊢ e1 :: τ →
               Δ , Σ' , Γ ⊢ e2 :: τ →
               Δ , Σ' , Γ ⊢ PBE:assert e1 e2 :: ⟨⟩

  mutual
    env : Set
    env = result ctx

    data _env-complete : env → Set where
      ENVC : ∀{E} → (∀{x rx} → (x , rx) ∈ E → rx rcomplete) → E env-complete

    data _env-final : env → Set where
      EF : ∀{E} → (∀{x rx} → (x , rx) ∈ E → rx final) → E env-final

    -- results - evaluation takes expressions to results, but results aren't necessarily final
    data result : Set where
      [_]fix_⦇·λ_=>_·⦈ : env → Nat → Nat → exp → result
      ⟨⟩               : result
      ⟨_,_⟩            : result → result → result
      C[_]_            : Nat → result → result
      [_]??[_]         : env → Nat → result
      _∘_              : result → result → result
      fst              : result → result
      snd              : result → result
      [_]case_of⦃·_·⦄ : env → result → rule ctx → result

    -- TODO maybe delete
    -- values are final and almost complete (i.e. they can only have holes in environments or under binders)
    data _value : result → Set where
      VFix  : ∀{E f x e} → E env-final → [ E ]fix f ⦇·λ x => e ·⦈ value
      VUnit : ⟨⟩ value
      VPair : ∀{r1 r2} → r1 final → r2 final → ⟨ r1 , r2 ⟩ value
      VCon  : ∀{c r} → r final → (C[ c ] r) value

    -- final results are those that cannot be evaluated further
    data _final : result → Set where
      FFix  : ∀{E f x e} → E env-final → [ E ]fix f ⦇·λ x => e ·⦈ final
      FUnit : ⟨⟩ final
      FPair : ∀{r1 r2} → r1 final → r2 final → ⟨ r1 , r2 ⟩ final
      FCon  : ∀{c r} → r final → (C[ c ] r) final
      FHole : ∀{E u} → E env-final → [ E ]??[ u ] final
      FAp   : ∀{r1 r2} → r1 final → r2 final → (∀{E f x e} → r1 ≠ [ E ]fix f ⦇·λ x => e ·⦈) → (r1 ∘ r2) final
      FFst  : ∀{r} → r final → (∀{r1 r2} → r ≠ ⟨ r1 , r2 ⟩) → (fst r) final
      FSnd  : ∀{r} → r final → (∀{r1 r2} → r ≠ ⟨ r1 , r2 ⟩) → (snd r) final
      FCase : ∀{E r rules} → r final → (∀{c r'} → r ≠ (C[ c ] r')) → E env-final → [ E ]case r of⦃· rules ·⦄ final

    -- complete results have no holes at all
    data _rcomplete : result → Set where
      RCFix  : ∀{E f x e} → E env-complete → e ecomplete → [ E ]fix f ⦇·λ x => e ·⦈ rcomplete
      RCUnit : ⟨⟩ rcomplete
      RCPair : ∀{r1 r2} → r1 rcomplete → r2 rcomplete → ⟨ r1 , r2 ⟩ rcomplete
      RCCtor : ∀{c r} → r rcomplete → (C[ c ] r) rcomplete
      RCAp   : ∀{r1 r2} → r1 rcomplete → r2 rcomplete → (r1 ∘ r2) rcomplete
      RCFst  : ∀{r} → r rcomplete → (fst r) rcomplete
      RCSnd  : ∀{r} → r rcomplete → (snd r) rcomplete
      RCCase : ∀{E r rules} →
                 E env-complete →
                 r rcomplete →
                 (∀{c rule} → (c , rule) ∈ rules → (rule.branch rule) ecomplete) →
                 [ E ]case r of⦃· rules ·⦄ rcomplete

    data _,_,_⊢_ : hctx → denv → tctx → env → Set where
      EnvId  : ∀{Δ Σ'} → Δ , Σ' , ∅ ⊢ ∅
      EnvInd : ∀{Δ Σ' Γ E x τx rx} →
                 Δ , Σ' , Γ ⊢ E →
                 Δ , Σ' ⊢ rx ·: τx →
                 Δ , Σ' , (Γ ,, (x , τx)) ⊢ (E ,, (x , rx))

    -- type assignment for results
    data _,_⊢_·:_ : hctx → denv → result → typ → Set where
      TAFix        : ∀{Δ Σ' Γ E f x e τ} →
                       Δ , Σ' , Γ ⊢ E →
                       Δ , Σ' , Γ ⊢ fix f ⦇·λ x => e ·⦈ :: τ →
                       Δ , Σ' ⊢ [ E ]fix f ⦇·λ x => e ·⦈ ·: τ
      TAApp        : ∀{Δ Σ' f arg τ1 τ2} →
                       Δ , Σ' ⊢ f ·: τ1 ==> τ2 →
                       Δ , Σ' ⊢ arg ·: τ1 →
                       Δ , Σ' ⊢ f ∘ arg ·: τ2
      TAUnit       : ∀{Δ Σ'} → Δ , Σ' ⊢ ⟨⟩ ·: ⟨⟩
      TAPair       : ∀{Δ Σ' r1 r2 τ1 τ2} →
                       Δ , Σ' ⊢ r1 ·: τ1 →
                       Δ , Σ' ⊢ r2 ·: τ2 →
                       Δ , Σ' ⊢ ⟨ r1 , r2 ⟩ ·: ⟨ τ1 × τ2 ⟩
      TAFst        : ∀{Δ Σ' r τ1 τ2} →
                       Δ , Σ' ⊢ r ·: ⟨ τ1 × τ2 ⟩ →
                       Δ , Σ' ⊢ fst r ·: τ1
      TASnd        : ∀{Δ Σ' r τ1 τ2} →
                       Δ , Σ' ⊢ r ·: ⟨ τ1 × τ2 ⟩ →
                       Δ , Σ' ⊢ snd r ·: τ2
      TACtor       : ∀{Δ Σ' d cctx c r τ} →
                       (d , cctx) ∈ π1 Σ' →
                       (c , τ) ∈ cctx →
                       Δ , Σ' ⊢ r ·: τ →
                       Δ , Σ' ⊢ C[ c ] r ·: D[ d ]
      TACase       : ∀{Δ Σ' Γ E d cctx r rules τ} →
                       (d , cctx) ∈ π1 Σ' →
                       Δ , Σ' , Γ ⊢ E →
                       Δ , Σ' ⊢ r ·: D[ d ] →
                       -- There must be a rule for each constructor, i.e. case exhaustiveness
                       (∀{c} → dom cctx c → dom rules c) →
                       (∀{c xc ec} →
                          (c , |C xc => ec) ∈ rules →
                            -- The constructor of each rule must be of the right datatype, and the branch must type-check
                            Σ[ τc ∈ typ ] (
                               (c , τc) ∈ cctx ∧
                               Δ , Σ' , (Γ ,, (xc , τc)) ⊢ ec :: τ)) →
                       Δ , Σ' ⊢ [ E ]case r of⦃· rules ·⦄ ·: τ
      TAHole       : ∀{Δ Σ' Γ E u τ} →
                       (u , (Γ , τ)) ∈ Δ →
                       Δ , Σ' , Γ ⊢ E →
                       Δ , Σ' ⊢ [ E ]??[ u ] ·: τ

  world         = env ∧ ex
  worlds        = List world
  assertions    = List (result ∧ val)
  constraints   = exp ctx ∧ worlds ctx
  hole-fillings = exp ctx

  record goal : Set where
    inductive
    constructor _⊢??[_]:_⊨_
    field
      g-tctx   : tctx
      g-id     : Nat
      g-typ    : typ
      g-worlds : worlds

  goals = List goal

  data Coerce_:=_ : result → val → Set where
    CoerceUnit : Coerce ⟨⟩ := ⟨⟩
    CoercePair : ∀{r1 r2 v1 v2} →
                   Coerce r1 := v1 →
                   Coerce r2 := v2 →
                   Coerce ⟨ r1 , r2 ⟩ := ⟨ v1 , v2 ⟩
    CoerceCtor : ∀{c r v} →
                   Coerce r := v →
                   Coerce C[ c ] r := C[ c ] v

  data LiftE_:=_ : val → exp → Set where
    LiftEUnit : LiftE ⟨⟩ := ⟨⟩
    LiftEPair : ∀{e1 e2 v1 v2} →
                  LiftE v1 := e1 →
                  LiftE v2 := e2 →
                  LiftE ⟨ v1 , v2 ⟩ := ⟨ e1 , e2 ⟩
    LiftECtor : ∀{c v e} →
                  LiftE v := e →
                  LiftE C[ c ] v := C[ c ] e

  -- worlds typing
  data _,_⊢_::ᵂ_,_ : hctx → denv → worlds → tctx → typ → Set where
    TAWNil : ∀{Δ Σ' Γ τ} → Δ , Σ' ⊢ [] ::ᵂ Γ , τ
    TAWRec : ∀{Δ Σ' W E ex Γ τ} →
               Δ , Σ' ⊢ W ::ᵂ Γ , τ →
               Δ , Σ' , Γ ⊢ E →
               Δ , Σ' ⊢ ex :· τ →
               Δ , Σ' ⊢ (E , ex) :: W ::ᵂ Γ , τ

  -- type checking for hole fillings
  data _,_⊢ₕ_ : hctx → denv → hole-fillings → Set where
    TANil      : ∀{Σ'} → ∅ , Σ' ⊢ₕ ∅
    TAHoleFill : ∀{Δ Σ' H u e Γ τ} →
                   Δ , Σ' ⊢ₕ H →
                   Δ , Σ' , Γ ⊢ e :: τ →
                   (Δ ,, (u , Γ , τ)) , Σ' ⊢ₕ (H ,, (u , e))

  -- constraints merge
  data _⊕_:=_ : constraints → constraints → constraints → Set where
    MergeNoWorlds : ∀{F1 F2} →
                      F1 ## F2 →
                      (F1 , ∅) ⊕ (F2 , ∅) := (F1 ∪ F2 , ∅)
    MergeLeft   : ∀{F1 U1 F2 U2 F3 U3 u W} →
                    (F1 , U1) ⊕ (F2 , U2) := (F3 , U3) →
                    u # U2 →
                    (F1 , U1 ,, (u , W)) ⊕ (F2 , U2) := (F3 , U3 ,, (u , W))
    MergeRight  : ∀{F1 U1 F2 U2 F3 U3 u W} →
                    (F1 , U1) ⊕ (F2 , U2) := (F3 , U3) →
                    u # U1 →
                    (F1 , U1) ⊕ (F2 , U2 ,, (u , W)) := (F3 , U3 ,, (u , W))
    MergeWorlds : ∀{F1 U1 F2 U2 F3 U3 u W1 W2} →
                    (F1 , U1) ⊕ (F2 , U2) := (F3 , U3) →
                    (F1 , U1 ,, (u , W1)) ⊕ (F2 , U2 ,, (u , W2)) := (F3 , U3 ,, (u , W1 ++ W2))

  -- hole substitution
  data _[_/??]:=_ : exp → hole-fillings → exp → Set where
    SHoleFill : ∀{H u e} → (u , e) ∈ H → ??[ u ] [ H /??]:= e
    SHoleUnf  : ∀{H u}   → u # H       → ??[ u ] [ H /??]:= ??[ u ]
    SFix      : ∀{H f x e e'} →
                  e [ H /??]:= e' →
                  (fix f ⦇·λ x => e ·⦈) [ H /??]:= (fix f ⦇·λ x => e' ·⦈)
    SVar      : ∀{H x} → X[ x ] [ H /??]:= X[ x ]
    SApp      : ∀{H ef ef' earg earg'} →
                  ef [ H /??]:= ef' →
                  earg [ H /??]:= earg' →
                  (ef ∘ earg) [ H /??]:= (ef' ∘ earg')
    SUnit     : ∀{H} → ⟨⟩ [ H /??]:= ⟨⟩
    SPair     : ∀{H e1 e1' e2 e2'} →
                  e1 [ H /??]:= e1' →
                  e2 [ H /??]:= e2' →
                  ⟨ e1 , e2 ⟩ [ H /??]:= ⟨ e1' , e2' ⟩
    SFst      : ∀{H e e'} →
                  e [ H /??]:= e' →
                  fst e [ H /??]:= fst e'
    SSnd      : ∀{H e e'} →
                  e [ H /??]:= e' →
                  snd e [ H /??]:= snd e'
    SCtor     : ∀{H c e e'} →
                  e [ H /??]:= e' →
                  (C[ c ] e) [ H /??]:= (C[ c ] e')
    SMatch    : ∀{H e e' rules rules'} →
                  (∀{c} → dom rules c → dom rules' c) →
                  (∀{c} → dom rules' c → dom rules c) →
                  e [ H /??]:= e' →
                  (∀{c x-c x-c' e-c e-c'} →
                     (c , |C x-c => e-c) ∈ rules →
                     (c , |C x-c' => e-c') ∈ rules' →
                     x-c == x-c' ∧ e-c [ H /??]:= e-c') →
                  case e of⦃· rules ·⦄ [ H /??]:= case e' of⦃· rules' ·⦄
    SAsrt     : ∀{H e1 e1' e2 e2'} →
                  e1 [ H /??]:= e1' →
                  e2 [ H /??]:= e2' →
                  PBE:assert e1 e2 [ H /??]:= PBE:assert e1' e2'

  not-both-pair : (r r' : result) → Set
  not-both-pair r r' = (∀{r1 r2} → r ≠ ⟨ r1 , r2 ⟩)  ∨ (∀{r1 r2} → r' ≠ ⟨ r1 , r2 ⟩)
  not-both-ctor : (r r' : result) → Set
  not-both-ctor r r' = (∀{c r''} → r ≠ (C[ c ] r'')) ∨ (∀{c r''} → r' ≠ (C[ c ] r''))

  -- result consistency
  data Constraints⦃_,_⦄:=_ : result → result → assertions → Set where
    RCRefl : ∀{r} → Constraints⦃ r , r ⦄:= []
    RCPair : ∀{r1 r2 r'1 r'2 A1 A2} →
               (_==_ {A = result} ⟨ r1 , r2 ⟩ ⟨ r'1 , r'2 ⟩ → ⊥) →
               Constraints⦃ r1 , r'1 ⦄:= A1 →
               Constraints⦃ r2 , r'2 ⦄:= A2 →
               Constraints⦃ ⟨ r1 , r2 ⟩ , ⟨ r'1 , r'2 ⟩ ⦄:= A1 ++ A2
    RCCtor : ∀{c r r' A} →
               (_==_ {A = result} (C[ c ] r) (C[ c ] r') → ⊥) →
               Constraints⦃ r , r' ⦄:= A →
               Constraints⦃ C[ c ] r , C[ c ] r' ⦄:= A
    RCVal1 : ∀{r r' v} →
               r ≠ r' →
               not-both-pair r r' →
               not-both-ctor r r' →
               Coerce r := v →
               Constraints⦃ r , r' ⦄:= ((r' , v) :: [])
    RCVal2 : ∀{r r' v'} →
               r ≠ r' →
               not-both-pair r r' →
               not-both-ctor r r' →
               Coerce r' := v' →
               Constraints⦃ r , r' ⦄:= ((r , v') :: [])

  -- Generic result consistency failure - this goes through if results are not consistent
  data Constraints⦃_,_⦄:=∅ : result → result → Set where
    RCFPair1    : ∀{r1 r2 r'1 r'2} →
                    Constraints⦃ r1 , r'1 ⦄:=∅ →
                    Constraints⦃ ⟨ r1 , r2 ⟩ , ⟨ r'1 , r'2 ⟩ ⦄:=∅
    RCFPair2    : ∀{r1 r2 r'1 r'2} →
                    Constraints⦃ r2 , r'2 ⦄:=∅ →
                    Constraints⦃ ⟨ r1 , r2 ⟩ , ⟨ r'1 , r'2 ⟩ ⦄:=∅
    RCFCtorMM   : ∀{c c' r r'} →
                    c ≠ c' →
                    Constraints⦃ C[ c ] r , C[ c' ] r' ⦄:=∅
    RCFCtor     : ∀{c r r'} →
                    Constraints⦃ r , r' ⦄:=∅ →
                    Constraints⦃ C[ c ] r , C[ c ] r' ⦄:=∅
    RCFNoCoerce : ∀{r r'} →
                    r ≠ r' →
                    not-both-pair r r' →
                    not-both-ctor r r' →
                    (∀{ex} → Coerce r  := ex → ⊥) →
                    (∀{ex} → Coerce r' := ex → ⊥) →
                    Constraints⦃ r , r' ⦄:=∅

  -- The evaluation, constraint collection, and backpropagation judgments accept "fuel",
  -- which defines whether or not they can recurse indefinitely, and, if not, then the
  -- numerical limit. The limit is not on the recursion depth, but rather on the number
  -- of "beta reductions", interpreted a bit loosely to include case evaluations.
  -- - If ⌊ ⛽ ⌋ is ∞, then there is no beta reduction limit,
  --   but the judgment will not be satisfied unless evaluation eventually terminates.
  -- - If ⌊ ⛽ ⌋ is ⛽⟨ n ⟩, then the beta reduction limit is at most n,
  --   but if the limit is reached, the evaluation and backpropagation judgments are
  --   satisfied automatically, whereas other judgments fail automatically
  data Fuel : Set where
    ∞ : Fuel
    ⛽⟨_⟩ : Nat → Fuel

  data _⛽⇓_ : Fuel → Fuel → Set where
    CF∞ : ∞ ⛽⇓ ∞
    CF⛽ : ∀{n} → ⛽⟨ 1+ n ⟩ ⛽⇓ ⛽⟨ n ⟩

  -- TODO we need a theorem that h-constraints cannot generate spurious hole names.
  -- generally, all the steps from an exp to an something with holes should not contain hole names
  -- not in the original exp, and the process as a whole should also not produce spurious names
  -- this realization probably means there are other important theorems that have been missed
  -- NOTE the core theorem in completeness.agda will do the trick for evaluation itself

  -- TODO we should have theorems that constrain where don't cares and such can be found.
  -- Don't cares should only be generated in backprop and should not appear anywhere else.

  -- Generic big step evaluation
  data _⊢_⌊_⌋⇒_⊣_ : env → exp → Fuel → result → assertions → Set where
    EFix             : ∀{E ⛽ f x e} → E ⊢ fix f ⦇·λ x => e ·⦈ ⌊ ⛽ ⌋⇒ [ E ]fix f ⦇·λ x => e ·⦈ ⊣ []
    EVar             : ∀{E ⛽ x r} → (x , r) ∈ E → E ⊢ X[ x ] ⌊ ⛽ ⌋⇒ r ⊣ []
    EHole            : ∀{E ⛽ u} → E ⊢ ??[ u ] ⌊ ⛽ ⌋⇒ [ E ]??[ u ] ⊣ []
    EUnit            : ∀{E ⛽} → E ⊢ ⟨⟩ ⌊ ⛽ ⌋⇒ ⟨⟩ ⊣ []
    EPair            : ∀{E ⛽ e1 e2 r1 r2 A1 A2} →
                         E ⊢ e1 ⌊ ⛽ ⌋⇒ r1 ⊣ A1 →
                         E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ A2 →
                         E ⊢ ⟨ e1 , e2 ⟩ ⌊ ⛽ ⌋⇒ ⟨ r1 , r2 ⟩ ⊣ A1 ++ A2
    ECtor            : ∀{E ⛽ c e r A} →
                         E ⊢ e ⌊ ⛽ ⌋⇒ r ⊣ A →
                         E ⊢ C[ c ] e ⌊ ⛽ ⌋⇒ (C[ c ] r) ⊣ A
    EAppFix          : ∀{E ⛽ ⛽↓ e1 e2 Ef f x ef r1 A1 r2 A2 r A} →
                         ⛽ ⛽⇓ ⛽↓ →
                         r1 == [ Ef ]fix f ⦇·λ x => ef ·⦈ →
                         E ⊢ e1 ⌊ ⛽ ⌋⇒ r1 ⊣ A1 →
                         E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ A2 →
                         (Ef ,, (f , r1) ,, (x , r2)) ⊢ ef ⌊ ⛽↓ ⌋⇒ r ⊣ A →
                         E ⊢ e1 ∘ e2 ⌊ ⛽ ⌋⇒ r ⊣ A1 ++ A2 ++ A
    EAppUnfinished   : ∀{E ⛽ e1 e2 r1 A1 r2 A2} →
                         E ⊢ e1 ⌊ ⛽ ⌋⇒ r1 ⊣ A1 →
                         (∀{Ef f x ef} → r1 ≠ [ Ef ]fix f ⦇·λ x => ef ·⦈) →
                         E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ A2 →
                         E ⊢ e1 ∘ e2 ⌊ ⛽ ⌋⇒ (r1 ∘ r2) ⊣ A1 ++ A2
    EFst             : ∀{E ⛽ e r1 r2 A} →
                         E ⊢ e ⌊ ⛽ ⌋⇒ ⟨ r1 , r2 ⟩ ⊣ A →
                         E ⊢ fst e ⌊ ⛽ ⌋⇒ r1 ⊣ A
    ESnd             : ∀{E ⛽ e r1 r2 A} →
                         E ⊢ e ⌊ ⛽ ⌋⇒ ⟨ r1 , r2 ⟩ ⊣ A →
                         E ⊢ snd e ⌊ ⛽ ⌋⇒ r2 ⊣ A
    EFstUnfinished   : ∀{E ⛽ e r A} →
                         E ⊢ e ⌊ ⛽ ⌋⇒ r ⊣ A →
                         (∀{r1 r2} → r ≠ ⟨ r1 , r2 ⟩) →
                         E ⊢ fst e ⌊ ⛽ ⌋⇒ fst r ⊣ A
    ESndUnfinished   : ∀{E ⛽ e r A} →
                         E ⊢ e ⌊ ⛽ ⌋⇒ r ⊣ A →
                         (∀{r1 r2} → r ≠ ⟨ r1 , r2 ⟩) →
                         E ⊢ snd e ⌊ ⛽ ⌋⇒ snd r ⊣ A
    EMatch           : ∀{E ⛽ ⛽↓ e rules c xc ec r' A' r A} →
                         ⛽ ⛽⇓ ⛽↓ →
                         (c , |C xc => ec) ∈ rules →
                         E ⊢ e ⌊ ⛽ ⌋⇒ (C[ c ] r') ⊣ A' →
                         (E ,, (xc , r')) ⊢ ec ⌊ ⛽↓ ⌋⇒ r ⊣ A →
                         E ⊢ case e of⦃· rules ·⦄ ⌊ ⛽ ⌋⇒ r ⊣ A' ++ A
    EMatchUnfinished : ∀{E ⛽ e rules r A} →
                         E ⊢ e ⌊ ⛽ ⌋⇒ r ⊣ A →
                         (∀{c e'} → r ≠ (C[ c ] e')) →
                         E ⊢ case e of⦃· rules ·⦄ ⌊ ⛽ ⌋⇒ [ E ]case r of⦃· rules ·⦄ ⊣ A
    EAsrt            : ∀{E ⛽ e1 r1 A1 e2 r2 A2 A3} →
                         E ⊢ e1 ⌊ ⛽ ⌋⇒ r1 ⊣ A1 →
                         E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ A2 →
                         Constraints⦃ r1 , r2 ⦄:= A3 →
                         E ⊢ PBE:assert e1 e2 ⌊ ⛽ ⌋⇒ ⟨⟩ ⊣ A1 ++ A2 ++ A3

  -- TODO failure cases may be out of date and need of update
  -- Generic evaluation failure - this goes through if evaluation would fail due to unsatisfiablility
  -- of a some constraint collection that occurs during evaluation, or if the fuel runs out.
  data _⊢_⌊_⌋⇒∅ : env → exp → Fuel → Set where
    EFPair1      : ∀{E ⛽ e1 e2} →
                     E ⊢ e1 ⌊ ⛽ ⌋⇒∅ →
                     E ⊢ ⟨ e1 , e2 ⟩ ⌊ ⛽ ⌋⇒∅
    EFPair2      : ∀{E ⛽ e1 e2} →
                     E ⊢ e2 ⌊ ⛽ ⌋⇒∅ →
                     E ⊢ ⟨ e1 , e2 ⟩ ⌊ ⛽ ⌋⇒∅
    EFCtor       : ∀{E ⛽ c e} →
                     E ⊢ e ⌊ ⛽ ⌋⇒∅ →
                     E ⊢ C[ c ] e ⌊ ⛽ ⌋⇒∅
    EFAppFun     : ∀{E ⛽ e1 e2} →
                     E ⊢ e1 ⌊ ⛽ ⌋⇒∅ →
                     E ⊢ e1 ∘ e2 ⌊ ⛽ ⌋⇒∅
    EFAppArg     : ∀{E ⛽ e1 e2} →
                     E ⊢ e2 ⌊ ⛽ ⌋⇒∅ →
                     E ⊢ e1 ∘ e2 ⌊ ⛽ ⌋⇒∅
    EFAppFixEval : ∀{E ⛽ ⛽↓ e1 e2 Ef f x ef r1 k1 r2 k2} →
                     ⛽ ⛽⇓ ⛽↓ →
                     r1 == [ Ef ]fix f ⦇·λ x => ef ·⦈ →
                     E ⊢ e1 ⌊ ⛽ ⌋⇒ r1 ⊣ k1 →
                     E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ k2 →
                     (Ef ,, (f , r1) ,, (x , r2)) ⊢ ef ⌊ ⛽↓ ⌋⇒∅ →
                     E ⊢ e1 ∘ e2 ⌊ ⛽ ⌋⇒∅
    EFFst        : ∀{E ⛽ e} →
                     E ⊢ e ⌊ ⛽ ⌋⇒∅ →
                     E ⊢ fst e ⌊ ⛽ ⌋⇒∅
    EFSnd        : ∀{E ⛽ e} →
                     E ⊢ e ⌊ ⛽ ⌋⇒∅ →
                     E ⊢ snd e ⌊ ⛽ ⌋⇒∅
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
    EFAsrt       : ∀{E ⛽ e1 r1 A1 e2 r2 A2} →
                     E ⊢ e1 ⌊ ⛽ ⌋⇒ r1 ⊣ A1 →
                     E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ A2 →
                     Constraints⦃ r1 , r2 ⦄:=∅ →
                     E ⊢ PBE:assert e1 e2 ⌊ ⛽ ⌋⇒∅
    EFLimit      : ∀{E e} → E ⊢ e ⌊ ⛽⟨ 0 ⟩ ⌋⇒∅

  -- resumption
  mutual
    data _⊢_⌊_⌋:⇨_ : hole-fillings → env → Fuel → env → Set where
      RENil : ∀{⛽ F} → F ⊢ ∅ ⌊ ⛽ ⌋:⇨ ∅
      REInd : ∀{⛽ F E E' x r r'} →
                F ⊢ E ⌊ ⛽ ⌋:⇨ E' →
                F ⊢ r ⌊ ⛽ ⌋⇨ r' →
                F ⊢ E ,, (x , r) ⌊ ⛽ ⌋:⇨ (E' ,, (x , r'))

    data _⊢_⌊_⌋⇨_ : hole-fillings → result → Fuel → result → Set where
      RFix           : ∀{⛽ H E E' f x e} →
                         H ⊢ E ⌊ ⛽ ⌋:⇨ E' →
                         H ⊢ [ E ]fix f ⦇·λ x => e ·⦈ ⌊ ⛽ ⌋⇨ [ E' ]fix f ⦇·λ x => e ·⦈
      RHoleFill      : ∀{⛽ H E u r r' e} →
                         (u , e) ∈ H →
                         E ⊢ e ⌊ ⛽ ⌋⇒ r ⊣ [] →
                         H ⊢ r ⌊ ⛽ ⌋⇨ r' →
                         H ⊢ [ E ]??[ u ] ⌊ ⛽ ⌋⇨ r'
      RHoleUnf       : ∀{⛽ H E E' u} →
                         u # H →
                         H ⊢ E ⌊ ⛽ ⌋:⇨ E' →
                         H ⊢ [ E ]??[ u ] ⌊ ⛽ ⌋⇨ [ E' ]??[ u ]
      RUnit          : ∀{⛽ H} → H ⊢ ⟨⟩ ⌊ ⛽ ⌋⇨ ⟨⟩
      RPair          : ∀{⛽ H r1 r2 r1' r2'} →
                         H ⊢ r1 ⌊ ⛽ ⌋⇨ r1' →
                         H ⊢ r2 ⌊ ⛽ ⌋⇨ r2' →
                         H ⊢ ⟨ r1 , r2 ⟩ ⌊ ⛽ ⌋⇨ ⟨ r1' , r2' ⟩
      RCtor          : ∀{⛽ H c r r'} →
                         H ⊢ r ⌊ ⛽ ⌋⇨ r' →
                         H ⊢ C[ c ] r ⌊ ⛽ ⌋⇨ (C[ c ] r')
      RApp           : ∀{⛽ ⛽↓ H rf rarg r r' Ef f x ef rf' rarg'} →
                         ⛽ ⛽⇓ ⛽↓ →
                         H ⊢ rf ⌊ ⛽ ⌋⇨ rf' →
                         rf' == [ Ef ]fix f ⦇·λ x => ef ·⦈ →
                         H ⊢ rarg ⌊ ⛽ ⌋⇨ rarg' →
                         (Ef ,, (f , rf') ,, (x , rarg')) ⊢ ef ⌊ ⛽↓ ⌋⇒ r ⊣ [] →
                         H ⊢ r ⌊ ⛽↓ ⌋⇨ r' →
                         H ⊢ rf ∘ rarg ⌊ ⛽ ⌋⇨ r'
      RAppUnf        : ∀{⛽ H rf rarg rf' rarg'} →
                         H ⊢ rf ⌊ ⛽ ⌋⇨ rf' →
                         (∀{E f x e} → rf' ≠ [ E ]fix f ⦇·λ x => e ·⦈) →
                         H ⊢ rarg ⌊ ⛽ ⌋⇨ rarg' →
                         H ⊢ rf ∘ rarg ⌊ ⛽ ⌋⇨ (rf' ∘ rarg')
      RFst           : ∀{⛽ H r r1 r2} →
                         H ⊢ r ⌊ ⛽ ⌋⇨ ⟨ r1 , r2 ⟩ →
                         H ⊢ fst r ⌊ ⛽ ⌋⇨ r1
      RFstUnf        : ∀{⛽ H r r'} →
                         H ⊢ r ⌊ ⛽ ⌋⇨ r' →
                         (∀{r1 r2} → r' ≠ ⟨ r1 , r2 ⟩) →
                         H ⊢ fst r ⌊ ⛽ ⌋⇨ fst r'
      RSnd           : ∀{⛽ H r r1 r2} →
                         H ⊢ r ⌊ ⛽ ⌋⇨ ⟨ r1 , r2 ⟩ →
                         H ⊢ snd r ⌊ ⛽ ⌋⇨ r2
      RSndUnf        : ∀{⛽ H r r'} →
                         H ⊢ r ⌊ ⛽ ⌋⇨ r' →
                         (∀{r1 r2} → r' ≠ ⟨ r1 , r2 ⟩) →
                         H ⊢ snd r ⌊ ⛽ ⌋⇨ snd r'
      RMatch         : ∀{⛽ H E r rules c xc ec r' rc} →
                         (c , |C xc => ec) ∈ rules →
                         H ⊢ r ⌊ ⛽ ⌋⇨ (C[ c ] r') →
                         H ⊢ [ E ]fix xc ⦇·λ xc => ec ·⦈ ∘ r' ⌊ ⛽ ⌋⇨ rc →
                         H ⊢ [ E ]case r of⦃· rules ·⦄ ⌊ ⛽ ⌋⇨ rc
      RMatchUnf      : ∀{⛽ H E E' r rules r'} →
                         H ⊢ r ⌊ ⛽ ⌋⇨ r' →
                         (∀{c r''} → r' ≠ (C[ c ] r'')) →
                         H ⊢ E ⌊ ⛽ ⌋:⇨ E' →
                         H ⊢ [ E ]case r of⦃· rules ·⦄ ⌊ ⛽ ⌋⇨ [ E' ]case r' of⦃· rules ·⦄

  -- Constraint, Example World, and Example Satisfaction

  data _,_⌊_⌋⊨ᴿ_ : hole-fillings → result → Fuel → ex → Set where
    XSNone  : ∀{⛽ H r} → H , r ⌊ ⛽ ⌋⊨ᴿ ¿¿
    XSUnit  : ∀{⛽ H} → H , ⟨⟩ ⌊ ⛽ ⌋⊨ᴿ ⟨⟩
    XSPair  : ∀{⛽ H r1 r2 ex1 ex2} →
                H , r1 ⌊ ⛽ ⌋⊨ᴿ ex1 →
                H , r2 ⌊ ⛽ ⌋⊨ᴿ ex2 →
                H , ⟨ r1 , r2 ⟩ ⌊ ⛽ ⌋⊨ᴿ ⟨ ex1 , ex2 ⟩
    XSCtor  : ∀{⛽ H r c ex} →
                H , r ⌊ ⛽ ⌋⊨ᴿ ex →
                H , C[ c ] r ⌊ ⛽ ⌋⊨ᴿ (C[ c ] ex)
    XSInOut : ∀{⛽ H r1 r2 v2 ex r} →
                 Coerce r2 := v2 →
                 H ⊢ r1 ∘ r2 ⌊ ⛽ ⌋⇨ r →
                 H , r ⌊ ⛽ ⌋⊨ᴿ ex →
                 H , r1 ⌊ ⛽ ⌋⊨ᴿ (v2 ↦ ex)

  data _,_⌊_⌋⊨ᴱ_ : hole-fillings → exp → Fuel → worlds → Set where
    CSEmpty      : ∀{⛽ H e} → H , e ⌊ ⛽ ⌋⊨ᴱ []
    CSConstraint : ∀{⛽ H e E ex W r r'} →
                     H , e ⌊ ⛽ ⌋⊨ᴱ W →
                     E ⊢ e ⌊ ⛽ ⌋⇒ r ⊣ [] →
                     H ⊢ r ⌊ ⛽ ⌋⇨ r' →
                     H , r' ⌊ ⛽ ⌋⊨ᴿ ex →
                     H , e ⌊ ⛽ ⌋⊨ᴱ ((E , ex) :: W)

  _⌊_⌋⊨_ : hole-fillings → Fuel → constraints → Set
  H ⌊ ⛽ ⌋⊨ (_ , U) = (u : Nat) (W : worlds) →
                      (u , W) ∈ U →
                      H , ??[ u ] ⌊ ⛽ ⌋⊨ᴱ W

  mutual
    -- example unevaluation
    data _,_⊢⦇_,_⊨_⦈⌊_⌋:=ᵁ_ : hctx → denv → hole-fillings → result → ex → Fuel → constraints → Set where
      XUNone       : ∀{⛽ Δ Σ' H r} → Δ , Σ' ⊢⦇ H , r ⊨ ¿¿ ⦈⌊ ⛽ ⌋:=ᵁ (∅ , ∅)
      XUUnit       : ∀{⛽ Δ Σ' H} → Δ , Σ' ⊢⦇ H , ⟨⟩ ⊨ ⟨⟩ ⦈⌊ ⛽ ⌋:=ᵁ (∅ , ∅)
      XUHole       : ∀{⛽ Δ Σ' H E u ex} →
                       ex ≠ ¿¿ →
                       Δ , Σ' ⊢⦇ H , [ E ]??[ u ] ⊨ ex ⦈⌊ ⛽ ⌋:=ᵁ (∅ , ■ (u , (E , ex) :: []))
      XUApp        : ∀{⛽ Δ Σ' H r1 r2 ex v2 K} →
                       ex ≠ ¿¿ →
                       Coerce r2 := v2 →
                       Δ , Σ' ⊢⦇ H , r1 ⊨ v2 ↦ ex ⦈⌊ ⛽ ⌋:=ᵁ K →
                       Δ , Σ' ⊢⦇ H , r1 ∘ r2 ⊨ ex ⦈⌊ ⛽ ⌋:=ᵁ K
      XUFix        : ∀{⛽ ⛽↓ Δ Σ' H E f x e rf varg rarg ex K} →
                       ⛽ ⛽⇓ ⛽↓ →
                       rf == [ E ]fix f ⦇·λ x => e ·⦈ →
                       Coerce rarg := varg →
                       Δ , Σ' ⊢⦇ H , e ⊨ ((E ,, (f , rf) ,, (x , rarg)) , ex) :: [] ⦈⌊ ⛽↓ ⌋:= K →
                       Δ , Σ' ⊢⦇ H , rf ⊨ varg ↦ ex ⦈⌊ ⛽ ⌋:=ᵁ K
      XUFst        : ∀{⛽ Δ Σ' H r ex K} →
                       ex ≠ ¿¿ →
                       Δ , Σ' ⊢⦇ H , r ⊨ ⟨ ex , ¿¿ ⟩ ⦈⌊ ⛽ ⌋:=ᵁ K →
                       Δ , Σ' ⊢⦇ H , fst r ⊨ ex ⦈⌊ ⛽ ⌋:=ᵁ K
      XUSnd        : ∀{⛽ Δ Σ' H r ex K} →
                       ex ≠ ¿¿ →
                       Δ , Σ' ⊢⦇ H , r ⊨ ⟨ ¿¿ , ex ⟩ ⦈⌊ ⛽ ⌋:=ᵁ K →
                       Δ , Σ' ⊢⦇ H , snd r ⊨ ex ⦈⌊ ⛽ ⌋:=ᵁ K
      XUMatch      : ∀{⛽ ⛽↓ Δ Σ' H F-guesses F' E r rules ex c-j x-j e-j r' K1 K2 K'} →
                       ex ≠ ¿¿ →
                       ⛽ ⛽⇓ ⛽↓ →
                       K1 ⊕ K2 := K' →
                       (c-j , |C x-j => e-j) ∈ rules →
                       Δ , Σ' ⊢ₕ F-guesses →
                       H ## F-guesses →
                       F' == H ∪ F-guesses →
                       F' ⊢ r ⌊ ⛽ ⌋⇨ (C[ c-j ] r') →
                       K1 == (F-guesses , ∅) →
                       Δ , Σ' ⊢⦇ F' , e-j ⊨ ((E ,, (x-j , r')) , ex) :: [] ⦈⌊ ⛽↓ ⌋:= K2 →
                       Δ , Σ' ⊢⦇ H , [ E ]case r of⦃· rules ·⦄ ⊨ ex ⦈⌊ ⛽ ⌋:=ᵁ K'
      XUPair       : ∀{⛽ Δ Σ' H r1 r2 ex1 ex2 K1 K2 K'} →
                       K1 ⊕ K2 := K' →
                       Δ , Σ' ⊢⦇ H , r1 ⊨ ex1 ⦈⌊ ⛽ ⌋:=ᵁ K1 →
                       Δ , Σ' ⊢⦇ H , r2 ⊨ ex2 ⦈⌊ ⛽ ⌋:=ᵁ K2 →
                       Δ , Σ' ⊢⦇ H , ⟨ r1 , r2 ⟩ ⊨ ⟨ ex1 , ex2 ⟩ ⦈⌊ ⛽ ⌋:=ᵁ K'
      XUCtor       : ∀{⛽ Δ Σ' H c r ex K} →
                       Δ , Σ' ⊢⦇ H , r ⊨ ex ⦈⌊ ⛽ ⌋:=ᵁ K →
                       Δ , Σ' ⊢⦇ H , C[ c ] r ⊨ C[ c ] ex ⦈⌊ ⛽ ⌋:=ᵁ K

    -- live bidirectional example satisfaction
    data _,_⊢⦇_,_⊨_⦈⌊_⌋:=_ : hctx → denv → hole-fillings → exp → worlds → Fuel → constraints → Set where
      SEmpty : ∀{⛽ Δ Σ' H e} → Δ , Σ' ⊢⦇ H , e ⊨ [] ⦈⌊ ⛽ ⌋:= (∅ , ∅)
      SInd   : ∀{⛽ Δ Σ' H e W K E ex r r' K' Kₘ} →
                 Δ , Σ' ⊢⦇ H , e ⊨ W ⦈⌊ ⛽ ⌋:= K →
                 E ⊢ e ⌊ ⛽ ⌋⇒ r ⊣ [] →
                 H ⊢ r ⌊ ⛽ ⌋⇨ r' →
                 Δ , Σ' ⊢⦇ H , r' ⊨ ex ⦈⌊ ⛽ ⌋:=ᵁ K' →
                 K' ⊕ K := Kₘ →
                 Δ , Σ' ⊢⦇ H , e ⊨ ((E , ex) :: W) ⦈⌊ ⛽ ⌋:= Kₘ

  -- TODO theorems for all the things, including resumption, synthesis, solve, satisfaction, consistency, Group, and Filter

  -- TODO proof that uneval(?) generalizes satisfaction stuff?

  -- Type-Directed Guessing
  data _⊢⦇_⊢??:_⦈:=ᴳ_ : denv → tctx → typ → exp → Set where
    GUnit  : ∀{Σ' Γ} → Σ' ⊢⦇ Γ ⊢??: ⟨⟩ ⦈:=ᴳ ⟨⟩
    GPair  : ∀{Σ' Γ τ1 τ2 e1 e2} →
               Σ' ⊢⦇ Γ ⊢??: τ1 ⦈:=ᴳ e1 →
               Σ' ⊢⦇ Γ ⊢??: τ2 ⦈:=ᴳ e2 →
               Σ' ⊢⦇ Γ ⊢??: ⟨ τ1 × τ2 ⟩ ⦈:=ᴳ ⟨ e1 , e2 ⟩
    GCtor  : ∀{Σ' Γ d cctx c τ e} →
               (d , cctx) ∈ π1 Σ' →
               (c , τ) ∈ cctx →
               Σ' ⊢⦇ Γ ⊢??: τ ⦈:=ᴳ e →
               Σ' ⊢⦇ Γ ⊢??: D[ d ] ⦈:=ᴳ (C[ c ] e)
    GFix   : ∀{Σ' Γ τ1 τ2 f x e} →
               Σ' ⊢⦇ Γ ,, (f , τ1 ==> τ2) ,, (x , τ1) ⊢??: τ2 ⦈:=ᴳ e →
               Σ' ⊢⦇ Γ ⊢??: τ1 ==> τ2 ⦈:=ᴳ fix f ⦇·λ x => e ·⦈
    GMatch : ∀{Σ' Γ τ e rules d cctx} →
               (d , cctx) ∈ π1 Σ' →
               (∀{c} → dom cctx c → dom rules c) →
               (∀{c} → dom rules c → dom cctx c) →
               Σ' ⊢⦇ Γ ⊢??: D[ d ] ⦈:=ᴳ e →
               (∀{c x-c e-c τ-c} →
                  (c , |C x-c => e-c) ∈ rules →
                  (c , τ-c) ∈ cctx →
                  Σ' ⊢⦇ Γ ,, (x-c , τ-c) ⊢??: τ ⦈:=ᴳ e-c) →
               Σ' ⊢⦇ Γ ⊢??: τ ⦈:=ᴳ case e of⦃· rules ·⦄
    GVar   : ∀{Σ' Γ τ x} →
               (x , τ) ∈ Γ →
               Σ' ⊢⦇ Γ ⊢??: τ ⦈:=ᴳ X[ x ]
    GApp   : ∀{Σ' Γ τ e1 e2 τ'} →
               Σ' ⊢⦇ Γ ⊢??: τ' ==> τ ⦈:=ᴳ e1 →
               Σ' ⊢⦇ Γ ⊢??: τ' ⦈:=ᴳ e2 →
               Σ' ⊢⦇ Γ ⊢??: τ ⦈:=ᴳ (e1 ∘ e2)
    GFst   : ∀{Σ' Γ τ1 τ2 e} →
               Σ' ⊢⦇ Γ ⊢??: ⟨ τ1 × τ2 ⟩ ⦈:=ᴳ e →
               Σ' ⊢⦇ Γ ⊢??: τ1 ⦈:=ᴳ fst e
    GSnd   : ∀{Σ' Γ τ1 τ2 e} →
               Σ' ⊢⦇ Γ ⊢??: ⟨ τ1 × τ2 ⟩ ⦈:=ᴳ e →
               Σ' ⊢⦇ Γ ⊢??: τ2 ⦈:=ᴳ snd e

  -- TODO theorem that if u # Δ , then u is new in a type-checked exp or result

  -- TODO change :=> back to := after we come up with a new symbol for constraints
  data Filter_:=>_ : worlds → worlds → Set where
    FilterNil : Filter [] :=> []
    FilterYes : ∀{W W' E ex} →
                  Filter W :=> W' →
                  ex ≠ ¿¿ →
                  Filter (E , ex) :: W :=> ((E , ex) :: W')
    FilterNo  : ∀{W W' E} →
                  Filter W :=> W' →
                  Filter (E , ¿¿) :: W :=> W'

  -- TODO theorem that any hole in the exp produced by refinement is in the goals

  -- Type-and-Example-Directed Refinement
  data _⊢⦇_⊢??:_⊨_⦈⌊_⌋:=ᴿ_⊣_ : denv → tctx → typ → worlds → Fuel → exp → goals → Set where
    IRUnit : ∀{⛽ Σ' Γ W Wf} →
               (∀{i w} → Wf ⟦ i ⟧ == Some w → π2 w == ⟨⟩) →
               Filter W :=> Wf →
               Σ' ⊢⦇ Γ ⊢??: ⟨⟩ ⊨ W ⦈⌊ ⛽ ⌋:=ᴿ ⟨⟩ ⊣ []
    IRPair : ∀{⛽ Σ' Γ τ1 τ2 W u1 u2 G1 G2} {E-ex1-ex2s : List (env ∧ ex ∧ ex)} →
               Filter W :=> map (λ {(E , ex1 , ex2) → E , ⟨ ex1 , ex2 ⟩}) E-ex1-ex2s →
               G1 == Γ ⊢??[ u1 ]: τ1 ⊨ map (λ {(E , ex1 , ex2) → E , ex1}) E-ex1-ex2s →
               G2 == Γ ⊢??[ u2 ]: τ2 ⊨ map (λ {(E , ex1 , ex2) → E , ex2}) E-ex1-ex2s →
               Σ' ⊢⦇ Γ ⊢??: ⟨ τ1 × τ2 ⟩ ⊨ W ⦈⌊ ⛽ ⌋:=ᴿ ⟨ ??[ u1 ] , ??[ u2 ] ⟩ ⊣ (G1 :: (G2 :: []))
    IRCtor : ∀{⛽ Σ' Γ W W' d cctx c τ u G} →
               (d , cctx) ∈ π1 Σ' →
               (c , τ) ∈ cctx →
               Filter W :=> map (λ {(E , ex) → E , C[ c ] ex}) W' →
               G == Γ ⊢??[ u ]: τ ⊨ W' →
               Σ' ⊢⦇ Γ ⊢??: D[ d ] ⊨ W ⦈⌊ ⛽ ⌋:=ᴿ C[ c ] ??[ u ] ⊣ (G :: [])
    IRFun   : ∀{⛽ Σ' Γ W τ1 τ2 f x u W' G} {E-in-inᶜ-outs : List (env ∧ val ∧ result ∧ ex)} →
                (∀{i E-i v-i r-i ex-i} →
                   E-in-inᶜ-outs ⟦ i ⟧ == Some (E-i , v-i , r-i , ex-i) →
                   Coerce r-i := v-i) →
                Filter W :=> map (λ {(E , in' , _ , out) → E , in' ↦ out}) E-in-inᶜ-outs →
                W' == map (λ {(E , _ , in' , out) → (E ,, (f , [ E ]fix f ⦇·λ x => ??[ u ] ·⦈) ,, (x , in')) , out}) E-in-inᶜ-outs →
                G == (Γ ,, (f , τ1 ==> τ2) ,, (x , τ1)) ⊢??[ u ]: τ2 ⊨ W' →
                Σ' ⊢⦇ Γ ⊢??: τ1 ==> τ2 ⊨ W ⦈⌊ ⛽ ⌋:=ᴿ fix f ⦇·λ x => ??[ u ] ·⦈ ⊣ (G :: [])
    IRMatch : ∀{⛽ Σ' Γ W Wf τ e rules d cctx x c+τ+u+W⁺s Gs} →
                Filter W :=> Wf →
                -- choose a datatype
                (d , cctx) ∈ π1 Σ' →
                -- for each constructor c of the chosen datatype, there is some item in c+τ+u+W⁺s
                -- that contains all the objects needed to construct the goal for that c
                (∀{c τ-c} →
                   (c , τ-c) ∈ cctx →
                   Σ[ i ∈ Nat ] Σ[ u-c ∈ Nat ] Σ[ W⁺-c ∈ List (env ∧ ex ∧ result) ]
                      (c+τ+u+W⁺s ⟦ i ⟧ == Some (c , τ-c , u-c , W⁺-c))) →
                (∀{i c τ-c u-c W⁺-c} →
                   c+τ+u+W⁺s ⟦ i ⟧ == Some (c , τ-c , u-c , W⁺-c) →
                   (c , τ-c) ∈ cctx) →
                -- choose one fresh variable name that will be used for all cases
                x # Γ →
                -- guess a scrutinee
                Σ' ⊢⦇ Γ ⊢??: D[ d ] ⦈:=ᴳ e →
                -- rules and Gs derive from the c+τ+u+W⁺s list
                rules == list⇒ctx (map (λ {(c , τ-c , u-c , W⁺-c) → (c , |C x => ??[ u-c ])}) c+τ+u+W⁺s) →
                Gs == map (λ {(c , τ-c , u-c , W⁺-c) → (Γ ,, (x , τ-c)) ⊢??[ u-c ]: τ ⊨ map (λ {(E , ex , r) → (E ,, (x , r)) , ex}) W⁺-c}) c+τ+u+W⁺s →
                -- For each constructor c, ...
                (∀{i c τ-c u-c W⁺-c} →
                   c+τ+u+W⁺s ⟦ i ⟧ == Some (c , τ-c , u-c , W⁺-c) →
                   -- for each world (extended with a result r-j) of W⁺-c, ...
                   (∀{j E-j ex-j r-j} →
                      W⁺-c ⟦ j ⟧ == Some (E-j , ex-j , r-j) →
                        -- the world is an element of Filter W, and ...
                        Σ[ k ∈ Nat ] (Wf ⟦ k ⟧ == Some (E-j , ex-j)) ∧
                        -- the scrutinee e will evaluate to constructor c applied to the specified argument r-j
                        E-j ⊢ e ⌊ ⛽ ⌋⇒ C[ c ] r-j ⊣ [])) →
                -- Every world in Filter W is an element of some W⁺-c for some c
                (∀{k E-k ex-k} →
                   Wf ⟦ k ⟧ == Some (E-k , ex-k) →
                   Σ[ i ∈ Nat ] Σ[ c ∈ Nat ] Σ[ τ-c ∈ typ ] Σ[ u-c ∈ Nat ] Σ[ W⁺-c ∈ List (env ∧ ex ∧ result)] Σ[ j ∈ Nat ] Σ[ r-j ∈ result ] (
                      c+τ+u+W⁺s ⟦ i ⟧ == Some (c , τ-c , u-c , W⁺-c) ∧
                      W⁺-c ⟦ j ⟧ == Some (E-k , ex-k , r-j))) →
                Σ' ⊢⦇ Γ ⊢??: τ ⊨ W ⦈⌊ ⛽ ⌋:=ᴿ case e of⦃· rules ·⦄ ⊣ Gs

  -- Hole Filling
  data _,_,_⊢⦇_⊢??[_]:_⊨_⦈⌊_⌋:=_,_ : hctx → denv → hole-fillings → tctx → Nat → typ → worlds → Fuel → constraints → hctx → Set where
    HFRefine  : ∀{⛽ Δ Σ' H Γ u τ W e Gs K Δ'} →
                  (∀{i j g-i g-j} →
                     Gs ⟦ i ⟧ == Some g-i →
                     Gs ⟦ j ⟧ == Some g-j →
                       goal.g-id g-i # Δ ∧
                       goal.g-id g-i ≠ u ∧
                       (i ≠ j → goal.g-id g-i ≠ goal.g-id g-j)) →
                  Σ' ⊢⦇ Γ ⊢??: τ ⊨ W ⦈⌊ ⛽ ⌋:=ᴿ e ⊣ Gs →
                  K == (■ (u , e) , list⇒ctx (map (λ {(_ ⊢??[ u' ]: _ ⊨ W') → u' , W'}) Gs)) →
                  Δ' == list⇒ctx (map (λ {(Γ' ⊢??[ u' ]: τ' ⊨ _) → u' , Γ' , τ'}) Gs) →
                  Δ , Σ' , H ⊢⦇ Γ ⊢??[ u ]: τ ⊨ W ⦈⌊ ⛽ ⌋:= K , Δ'
    HFGuess   : ∀{⛽ Δ Σ' H Γ u τ W e K K'} →
                  Σ' ⊢⦇ Γ ⊢??: τ ⦈:=ᴳ e →
                  Δ , Σ' ⊢⦇ (H ,, (u , e)) , e ⊨ W ⦈⌊ ⛽ ⌋:= K →
                  (■ (u , e) , ∅) ⊕ K := K' →
                  Δ , Σ' , H ⊢⦇ Γ ⊢??[ u ]: τ ⊨ W ⦈⌊ ⛽ ⌋:= K' , ∅
    HFNothing : ∀{⛽ Δ Σ' H Γ u τ W} →
                  W ≠ [] →
                  Filter W :=> [] →
                  Δ , Σ' , H ⊢⦇ Γ ⊢??[ u ]: τ ⊨ W ⦈⌊ ⛽ ⌋:= (■ (u , ??[ u ]) , ∅) , ∅

  data _,_IterSolve_,_⌊_⌋:=_,_ : hctx → denv → hole-fillings → worlds ctx → Fuel → hole-fillings → hctx → Set where
    ISFin : ∀{⛽ Δ Σ' F-0 U F' Δ' u+F+Δs} →
              (∀{u} → dom U u → dom Δ u) →
              ∥ u+F+Δs ∥ == 1+ ∥ U ∥ →
              Σ[ u-0 ∈ Nat ] (u+F+Δs ⟦ 0 ⟧ == Some (u-0 , F-0 , Δ)) →
              (∀{u W} →
                 (u , W) ∈ U →
                 Σ[ i ∈ Nat ] Σ[ F-i ∈ hole-fillings ] Σ[ Δ-i ∈ hctx ] (
                    1+ i < ∥ u+F+Δs ∥ ∧ u+F+Δs ⟦ i ⟧ == Some (u , F-i , Δ-i))) →
              (∀{i u-i u-i+1 W-i F-i F-i+1 Δ-i Δ-i+1 Γ-i τ-i} →
                 1+ i < ∥ u+F+Δs ∥ →
                 u+F+Δs ⟦ i ⟧    == Some (u-i , F-i , Δ-i) →
                 u+F+Δs ⟦ 1+ i ⟧ == Some (u-i+1 , F-i+1 , Δ-i+1) →
                 (u-i , W-i) ∈ U →
                 (u-i , Γ-i , τ-i) ∈ Δ →
                 Σ[ F'-i ∈ hole-fillings ] Σ[ Δ'-i ∈ hctx ] (
                    (Δ-i , Σ' , F-i ⊢⦇ Γ-i ⊢??[ u-i ]: τ-i ⊨ W-i ⦈⌊ ⛽ ⌋:= (F'-i , ∅) , Δ'-i) ∧
                    F-i+1 == F-i ∪ F'-i ∧
                    Δ-i+1 == Δ-i ∪ Δ'-i)) →
              Σ[ u-n ∈ Nat ] (u+F+Δs ⟦ ∥ U ∥ ⟧ == Some (u-n , F' , Δ')) →
              Δ , Σ' IterSolve F-0 , U ⌊ ⛽ ⌋:= F' , Δ'
    ISInd : ∀{⛽ Δ Σ' F-0 U F' Δ' u+F+U+Δs U' Δ-n F-n} →
              (∀{u} → dom U u → dom Δ u) →
              ∥ u+F+U+Δs ∥ == 1+ ∥ U ∥ →
              Σ[ u-0 ∈ Nat ] (u+F+U+Δs ⟦ 0 ⟧ == Some (u-0 , F-0 , ∅ , Δ)) →
              (∀{u W} →
                 (u , W) ∈ U →
                 Σ[ i ∈ Nat ] Σ[ F-i ∈ hole-fillings ] Σ[ U-i ∈ worlds ctx ] Σ[ Δ-i ∈ hctx ] (
                    1+ i < ∥ u+F+U+Δs ∥ ∧ u+F+U+Δs ⟦ i ⟧ == Some (u , F-i , U-i , Δ-i))) →
              (∀{i u-i u-i+1 W-i F-i F-i+1 U-i U-i+1 Δ-i Δ-i+1 Γ-i τ-i} →
                 1+ i < ∥ u+F+U+Δs ∥ →
                 u+F+U+Δs ⟦ i ⟧    == Some (u-i , F-i , U-i , Δ-i) →
                 u+F+U+Δs ⟦ 1+ i ⟧ == Some (u-i+1 , F-i+1 , U-i+1 , Δ-i+1) →
                 (u-i , W-i) ∈ U →
                 (u-i , Γ-i , τ-i) ∈ Δ →
                 Σ[ F'-i ∈ hole-fillings ] Σ[ Δ'-i ∈ hctx ] (
                    (Δ-i , Σ' , F-i ⊢⦇ Γ-i ⊢??[ u-i ]: τ-i ⊨ W-i ⦈⌊ ⛽ ⌋:= (F'-i , U-i+1) , Δ'-i) ∧
                    F-i+1 == F-i ∪ F'-i ∧
                    Δ-i+1 == Δ-i ∪ Δ'-i)) →
              U' == foldl _∪_ ∅ (map (π1 ⊙ (π2 ⊙ π2)) u+F+U+Δs) →
              U' ≠ ∅ →
              Σ[ u-n ∈ Nat ] Σ[ U-n ∈ worlds ctx ] (u+F+U+Δs ⟦ ∥ U ∥ ⟧ == Some (u-n , F-n , U-n , Δ-n)) →
              Δ-n , Σ' IterSolve F-n , U' ⌊ ⛽ ⌋:= F' , Δ' →
              Δ , Σ' IterSolve F-0 , U ⌊ ⛽ ⌋:= F' , Δ'

  data _,_Solve_⌊_⌋:=_ : hctx → denv → constraints → Fuel → hole-fillings → Set where
    Solve : ∀{⛽ Δ Σ' F0 U F Δ'} →
              Δ , Σ' IterSolve F0 , U ⌊ ⛽ ⌋:= F , Δ' →
              Δ , Σ' Solve (F0 , U) ⌊ ⛽ ⌋:= F

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
