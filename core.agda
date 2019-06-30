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
      ⟨⟩    : ex
      ⟨_,_⟩ : ex → ex → ex
      C[_]_ : Nat → ex → ex
      _↦_  : result → ex → ex
      ¿¿    : ex

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
      TAMap  : ∀{Δ Σ' r ex τ1 τ2} →
                 Δ , Σ' ⊢ r ·: τ1 →
                 Δ , Σ' ⊢ ex :· τ2 →
                 Δ , Σ' ⊢ r ↦ ex :· τ1 ==> τ2

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
      C⁻[_]_           : Nat → result → result
      [_]??[_]         : env → Nat → result
      _∘_              : result → result → result
      fst              : result → result
      snd              : result → result
      [_]case_of⦃·_·⦄ : env → result → rule ctx → result

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
      FCInv : ∀{c r} → r final → (C⁻[ c ] r ) final
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
      TAUnwrapCtor : ∀{Δ Σ' d cctx c r τ} →
                       (d , cctx) ∈ π1 Σ' →
                       (c , τ) ∈ cctx →
                       Δ , Σ' ⊢ r ·: D[ d ] →
                       Δ , Σ' ⊢ C⁻[ c ] r ·: τ
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

  world       = env ∧ ex
  worlds      = List world
  -- TODO how-will-we/do-we-need-to restrict constraints so that it only has undets and not other results?
  constraints = List (result ∧ ex)

  not-both-pair : (r r' : result) → Set
  not-both-pair r r' = (∀{r1 r2} → r ≠ ⟨ r1 , r2 ⟩)  ∨ (∀{r1 r2} → r' ≠ ⟨ r1 , r2 ⟩)
  not-both-ctor : (r r' : result) → Set
  not-both-ctor r r' = (∀{c r''} → r ≠ (C[ c ] r'')) ∨ (∀{c r''} → r' ≠ (C[ c ] r''))

  data Coerce_:=_ : result → ex → Set where
    CoerceUnit : Coerce ⟨⟩ := ⟨⟩
    CoercePair : ∀{r1 r2 ex1 ex2} →
                   Coerce r1 := ex1 →
                   Coerce r2 := ex2 →
                   Coerce ⟨ r1 , r2 ⟩ := ⟨ ex1 , ex2 ⟩
    CoerceCtor : ∀{c r ex} →
                   Coerce r := ex →
                   Coerce C[ c ] r := C[ c ] ex

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

  mutual
    -- constraint collection
    data Constraints⦃_,_⦄⌊_⌋:=_ : result → result → Fuel → constraints → Set where
      -- TODO try to make refl come after ctor and pair
      XCExRefl    : ∀{⛽ r} → Constraints⦃ r , r ⦄⌊ ⛽ ⌋:= []
      XCPair      : ∀{⛽ r1 r2 r'1 r'2 k1 k2} →
                      (_==_ {A = result} ⟨ r1 , r2 ⟩ ⟨ r'1 , r'2 ⟩ → ⊥) →
                      Constraints⦃ r1 , r'1 ⦄⌊ ⛽ ⌋:= k1 →
                      Constraints⦃ r2 , r'2 ⦄⌊ ⛽ ⌋:= k2 →
                      Constraints⦃ ⟨ r1 , r2 ⟩ , ⟨ r'1 , r'2 ⟩ ⦄⌊ ⛽ ⌋:= k1 ++ k2
      XCCtor      : ∀{⛽ c r r' k} →
                      (_==_ {A = result} (C[ c ] r) (C[ c ] r') → ⊥) →
                      Constraints⦃ r , r' ⦄⌊ ⛽ ⌋:= k →
                      Constraints⦃ C[ c ] r , C[ c ] r' ⦄⌊ ⛽ ⌋:= k
      XCBackProp1 : ∀{⛽ ex k} {r r' : result} →
                      r ≠ r' →
                      not-both-pair r r' →
                      not-both-ctor r r' →
                      Coerce r' := ex →
                      r ⇐ ex ⌊ ⛽ ⌋:= k →
                      Constraints⦃ r , r' ⦄⌊ ⛽ ⌋:= k
      XCBackProp2 : ∀{⛽ r r' ex k} →
                      r ≠ r' →
                      not-both-pair r r' →
                      not-both-ctor r r' →
                      Coerce r := ex →
                      r' ⇐ ex ⌊ ⛽ ⌋:= k →
                      Constraints⦃ r , r' ⦄⌊ ⛽ ⌋:= k

    -- TODO we need a theorem that constraints cannot generate spurious hole names.
    -- generally, all the steps from an exp to an something with holes should not contain hole names
    -- not in the original exp, and the process as a whole should also not produce spurious names
    -- this realization probably means there are other important theorems that have been missed
    -- NOTE the core theorem in completeness.agda will do the trick for evaluation itself

    -- TODO we should have theorems that constrain where don't cares and such can be found.
    -- Don't cares should only be generated in backprop and should not appear anywhere else.

    -- TODO we should also have similar to the above for C⁻

    -- backpropagation
    data _⇐_⌊_⌋:=_ : result → ex → Fuel → constraints → Set where
      XBNone       : ∀{⛽ r} → r ⇐ ¿¿ ⌊ ⛽ ⌋:= []
      XBHole       : ∀{⛽ E u ex} →
                       ex ≠ ¿¿ →
                       [ E ]??[ u ] ⇐ ex ⌊ ⛽ ⌋:= (([ E ]??[ u ] , ex) :: [])
      XBApp        : ∀{⛽ r1 r2 ex k} →
                       ex ≠ ¿¿ →
                       r1 ⇐ r2 ↦ ex ⌊ ⛽ ⌋:= k →
                       (r1 ∘ r2) ⇐ ex ⌊ ⛽ ⌋:= k
      XBFixDC      : ∀{⛽ ⛽↓ E f x e rf rarg ex v k1 k2} →
                       ⛽ ⛽⇓ ⛽↓ →
                       rf == [ E ]fix f ⦇·λ x => e ·⦈ →
                       (E ,, (f , rf) ,, (x , rarg)) ⊢ e ⌊ ⛽↓ ⌋⇒ v ⊣ k1 →
                       v value →
                       v ⇐ ex ⌊ ⛽↓ ⌋:= k2 →
                       rf ⇐ rarg ↦ ex ⌊ ⛽ ⌋:= k1 ++ k2
      XBFixDL      : ∀{⛽ ⛽↓ E f x e rf rarg ex r k} →
                       ⛽ ⛽⇓ ⛽↓ →
                       rf == [ E ]fix f ⦇·λ x => e ·⦈ →
                       (E ,, (f , rf) ,, (x , rarg)) ⊢ e ⌊ ⛽↓ ⌋⇒ r ⊣ k →
                       (r value → ⊥) →
                       rf ⇐ rarg ↦ ex ⌊ ⛽ ⌋:= k ++ ((r , ex) :: [])
      XBFst        : ∀{⛽ r ex1 k} →
                       ex1 ≠ ¿¿ →
                       r ⇐ ⟨ ex1 , ¿¿ ⟩ ⌊ ⛽ ⌋:= k →
                       fst r ⇐ ex1 ⌊ ⛽ ⌋:= k
      XBSnd        : ∀{⛽ r ex2 k} →
                       ex2 ≠ ¿¿ →
                       r ⇐ ⟨ ¿¿ , ex2 ⟩ ⌊ ⛽ ⌋:= k →
                       snd r ⇐ ex2 ⌊ ⛽ ⌋:= k
      XBMatch      : ∀{⛽ ⛽↓ E r rules ex c-j x-j e-j r-j k1 k2 k3} →
                       ⛽ ⛽⇓ ⛽↓ →
                       ex ≠ ¿¿ →
                       (c-j , |C x-j => e-j) ∈ rules →
                       r ⇐ C[ c-j ] ¿¿ ⌊ ⛽ ⌋:= k1 →
                       (E ,, (x-j , C⁻[ c-j ] r)) ⊢ e-j ⌊ ⛽↓ ⌋⇒ r-j ⊣ k2 →
                       r-j ⇐ ex ⌊ ⛽↓ ⌋:= k3 →
                       [ E ]case r of⦃· rules ·⦄ ⇐ ex ⌊ ⛽ ⌋:= k1 ++ k2 ++ k3
      XBUnwrapCtor : ∀{⛽ c r ex k} →
                       ex ≠ ¿¿ →
                       r ⇐ C[ c ] ex ⌊ ⛽ ⌋:= k →
                       (C⁻[ c ] r) ⇐ ex ⌊ ⛽ ⌋:= k
      XBUnit       : ∀{⛽} → ⟨⟩ ⇐ ⟨⟩ ⌊ ⛽ ⌋:= []
      XBPair       : ∀{⛽ r1 r2 ex1 ex2 k1 k2} →
                       r1 ⇐ ex1 ⌊ ⛽ ⌋:= k1 →
                       r2 ⇐ ex2 ⌊ ⛽ ⌋:= k2 →
                       ⟨ r1 , r2 ⟩ ⇐ ⟨ ex1 , ex2 ⟩ ⌊ ⛽ ⌋:= k1 ++ k2
      XBCtor       : ∀{⛽ c r ex k} →
                       r ⇐ ex ⌊ ⛽ ⌋:= k →
                       (C[ c ] r) ⇐ C[ c ] ex ⌊ ⛽ ⌋:= k
      XBLimit      : ∀{r ex} → r ⇐ ex ⌊ ⛽⟨ 0 ⟩ ⌋:= []

    -- Generic big step evaluation
    data _⊢_⌊_⌋⇒_⊣_ : env → exp → Fuel → result → constraints → Set where
      EFix             : ∀{E ⛽ f x e} → E ⊢ fix f ⦇·λ x => e ·⦈ ⌊ ⛽ ⌋⇒ [ E ]fix f ⦇·λ x => e ·⦈ ⊣ []
      EVar             : ∀{E ⛽ x r} → (x , r) ∈ E → E ⊢ X[ x ] ⌊ ⛽ ⌋⇒ r ⊣ []
      EHole            : ∀{E ⛽ u} → E ⊢ ??[ u ] ⌊ ⛽ ⌋⇒ [ E ]??[ u ] ⊣ []
      EUnit            : ∀{E ⛽} → E ⊢ ⟨⟩ ⌊ ⛽ ⌋⇒ ⟨⟩ ⊣ []
      EPair            : ∀{E ⛽ e1 e2 r1 r2 k1 k2} →
                           E ⊢ e1 ⌊ ⛽ ⌋⇒ r1 ⊣ k1 →
                           E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ k2 →
                           E ⊢ ⟨ e1 , e2 ⟩ ⌊ ⛽ ⌋⇒ ⟨ r1 , r2 ⟩ ⊣ k1 ++ k2
      ECtor            : ∀{E ⛽ c e r k} →
                           E ⊢ e ⌊ ⛽ ⌋⇒ r ⊣ k →
                           E ⊢ C[ c ] e ⌊ ⛽ ⌋⇒ (C[ c ] r) ⊣ k
      EAppFix          : ∀{E ⛽ ⛽↓ e1 e2 Ef f x ef r1 k1 r2 k2 r k} →
                           ⛽ ⛽⇓ ⛽↓ →
                           r1 == [ Ef ]fix f ⦇·λ x => ef ·⦈ →
                           E ⊢ e1 ⌊ ⛽ ⌋⇒ r1 ⊣ k1 →
                           E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ k2 →
                           (Ef ,, (f , r1) ,, (x , r2)) ⊢ ef ⌊ ⛽↓ ⌋⇒ r ⊣ k →
                           E ⊢ e1 ∘ e2 ⌊ ⛽ ⌋⇒ r ⊣ k1 ++ k2 ++ k
      EAppUnfinished   : ∀{E ⛽ e1 e2 r1 k1 r2 k2} →
                           E ⊢ e1 ⌊ ⛽ ⌋⇒ r1 ⊣ k1 →
                           (∀{Ef f x ef} → r1 ≠ [ Ef ]fix f ⦇·λ x => ef ·⦈) →
                           E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ k2 →
                           E ⊢ e1 ∘ e2 ⌊ ⛽ ⌋⇒ (r1 ∘ r2) ⊣ k1 ++ k2
      EFst             : ∀{E ⛽ e r1 r2 k} →
                           E ⊢ e ⌊ ⛽ ⌋⇒ ⟨ r1 , r2 ⟩ ⊣ k →
                           E ⊢ fst e ⌊ ⛽ ⌋⇒ r1 ⊣ k
      ESnd             : ∀{E ⛽ e r1 r2 k} →
                           E ⊢ e ⌊ ⛽ ⌋⇒ ⟨ r1 , r2 ⟩ ⊣ k →
                           E ⊢ snd e ⌊ ⛽ ⌋⇒ r2 ⊣ k
      EFstUnfinished   : ∀{E ⛽ e r k} →
                           E ⊢ e ⌊ ⛽ ⌋⇒ r ⊣ k →
                           (∀{r1 r2} → r ≠ ⟨ r1 , r2 ⟩) →
                           E ⊢ fst e ⌊ ⛽ ⌋⇒ fst r ⊣ k
      ESndUnfinished   : ∀{E ⛽ e r k} →
                           E ⊢ e ⌊ ⛽ ⌋⇒ r ⊣ k →
                           (∀{r1 r2} → r ≠ ⟨ r1 , r2 ⟩) →
                           E ⊢ snd e ⌊ ⛽ ⌋⇒ snd r ⊣ k
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
      EAsrt            : ∀{E ⛽ e1 r1 k1 e2 r2 k2 k3} →
                           E ⊢ e1 ⌊ ⛽ ⌋⇒ r1 ⊣ k1 →
                           E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ k2 →
                           Constraints⦃ r1 , r2 ⦄⌊ ⛽ ⌋:= k3 →
                           E ⊢ PBE:assert e1 e2 ⌊ ⛽ ⌋⇒ ⟨⟩ ⊣ k1 ++ k2 ++ k3
      ELimit           : ∀{E e r} → E ⊢ e ⌊ ⛽⟨ 0 ⟩ ⌋⇒ r ⊣ []

  -- Constraints collection - the ordinary variety with no beta reduction counting or limit
  Constraints⦃_,_⦄:=_ : result → result → constraints → Set
  Constraints⦃ r1 , r2 ⦄:= k = Constraints⦃ r1 , r2 ⦄⌊ ∞ ⌋:= k

  -- Backpropagation - the ordinary variety with no beta reduction counting or limit
  _⇐_:=_ : result → ex → constraints → Set
  r ⇐ ex := k = r ⇐ ex ⌊ ∞ ⌋:= k

  -- Big step evaluation - the ordinary variety with no beta reduction counting or limit
  _⊢_⇒_⊣_ : env → exp → result → constraints → Set
  E ⊢ e ⇒ r ⊣ k = E ⊢ e ⌊ ∞ ⌋⇒ r ⊣ k

  -- TODO failure cases have not been updated since major paper changes
  mutual
    -- Constraint collection failure - see the comment for "Generic evaluation failure"
    data Constraints⦃_,_⦄⌊_⌋:=∅ : result → result → Fuel → Set where
      XCFPair1    : ∀{⛽ r1 r2 r'1 r'2} →
                      Constraints⦃ r1 , r'1 ⦄⌊ ⛽ ⌋:=∅ →
                      Constraints⦃ ⟨ r1 , r2 ⟩ , ⟨ r'1 , r'2 ⟩ ⦄⌊ ⛽ ⌋:=∅
      XCFPair2    : ∀{⛽ r1 r2 r'1 r'2} →
                      Constraints⦃ r2 , r'2 ⦄⌊ ⛽ ⌋:=∅ →
                      Constraints⦃ ⟨ r1 , r2 ⟩ , ⟨ r'1 , r'2 ⟩ ⦄⌊ ⛽ ⌋:=∅
      XCFCtorMM   : ∀{⛽ c c' r r'} →
                      c ≠ c' →
                      Constraints⦃ C[ c ] r , C[ c' ] r' ⦄⌊ ⛽ ⌋:=∅
      XCFCtor     : ∀{⛽ c r r'} →
                      Constraints⦃ r , r' ⦄⌊ ⛽ ⌋:=∅ →
                      Constraints⦃ C[ c ] r , C[ c ] r' ⦄⌊ ⛽ ⌋:=∅
      XCFXB1      : ∀{⛽ r r' ex} →
                      r ≠ r' →
                      not-both-pair r r' →
                      not-both-ctor r r' →
                      Coerce r' := ex →
                      r ⇐ ex ⌊ ⛽ ⌋:=∅ →
                      Constraints⦃ r , r' ⦄⌊ ⛽ ⌋:=∅
      XCFXB2      : ∀{⛽ r r' ex} →
                      r ≠ r' →
                      not-both-pair r r' →
                      not-both-ctor r r' →
                      Coerce r := ex →
                      r' ⇐ ex ⌊ ⛽ ⌋:=∅ →
                      Constraints⦃ r , r' ⦄⌊ ⛽ ⌋:=∅
      XCFNoCoerce : ∀{⛽ r r'} →
                      r ≠ r' →
                      not-both-pair r r' →
                      not-both-ctor r r' →
                      (∀{ex} → Coerce r  := ex → ⊥) →
                      (∀{ex} → Coerce r' := ex → ⊥) →
                      Constraints⦃ r , r' ⦄⌊ ⛽ ⌋:=∅

    -- backpropagation failure - see the comment for "Generic evaluation failure"
    -- TODO for this and xc failure, we should describe all the failure cases that we've gone to the effort
    --      to positively characterize
    data _⇐_⌊_⌋:=∅ : result → ex → Fuel → Set where
      XBFHole       : ∀{⛽ E u v ex} → [ E ]??[ u ] ⇐ v ↦ ex ⌊ ⛽ ⌋:=∅
      XBFPair1      : ∀{⛽ r1 r2 ex1 ex2} →
                        r1 ⇐ ex1 ⌊ ⛽ ⌋:=∅ →
                        ⟨ r1 , r2 ⟩ ⇐ ⟨ ex1 , ex2 ⟩ ⌊ ⛽ ⌋:=∅
      XBFPair2      : ∀{⛽ r1 r2 ex1 ex2} →
                        r2 ⇐ ex2 ⌊ ⛽ ⌋:=∅ →
                        ⟨ r1 , r2 ⟩ ⇐ ⟨ ex1 , ex2 ⟩ ⌊ ⛽ ⌋:=∅
      XBFCtorMM     : ∀{⛽ c c' r ex} →
                        c ≠ c' →
                        (C[ c ] r) ⇐ C[ c' ] ex ⌊ ⛽ ⌋:=∅
      XBFCtor       : ∀{⛽ c r ex} →
                        r ⇐ ex ⌊ ⛽ ⌋:=∅ →
                        (C[ c ] r) ⇐ C[ c ] ex ⌊ ⛽ ⌋:=∅
      XBFAppNonVal  : ∀{⛽ r1 r2 ex} →
                        ex ≠ ¿¿ →
                        (r2 value → ⊥) →
                        (r1 ∘ r2) ⇐ ex ⌊ ⛽ ⌋:=∅
      XBFApp        : ∀{⛽ r v ex} →
                        ex ≠ ¿¿ →
                        v value →
                        r ⇐ v ↦ ex ⌊ ⛽ ⌋:=∅ →
                        (r ∘ v) ⇐ ex ⌊ ⛽ ⌋:=∅
      XBFFixEval    : ∀{⛽ ⛽↓ E f x e rf v ex} →
                        ⛽ ⛽⇓ ⛽↓ →
                        rf == [ E ]fix f ⦇·λ x => e ·⦈ →
                        (E ,, (f , rf) ,, (x , v)) ⊢ e ⌊ ⛽↓ ⌋⇒∅ →
                        rf ⇐ v ↦ ex ⌊ ⛽ ⌋:=∅
      XBFFix        : ∀{⛽ ⛽↓ E f x e rf v ex r k} →
                        ⛽ ⛽⇓ ⛽↓ →
                        rf == [ E ]fix f ⦇·λ x => e ·⦈ →
                        (E ,, (f , rf) ,, (x , v)) ⊢ e ⌊ ⛽↓ ⌋⇒ r ⊣ k →
                        r ⇐ ex ⌊ ⛽↓ ⌋:=∅ →
                        rf ⇐ v ↦ ex ⌊ ⛽ ⌋:=∅
      XBFFst        : ∀{⛽ r ex1} →
                        ex1 ≠ ¿¿ →
                        r ⇐ ⟨ ex1 , ¿¿ ⟩ ⌊ ⛽ ⌋:=∅ →
                        fst r ⇐ ex1 ⌊ ⛽ ⌋:=∅
      XBFSnd        : ∀{⛽ r ex2} →
                        ex2 ≠ ¿¿ →
                        r ⇐ ⟨ ¿¿ , ex2 ⟩ ⌊ ⛽ ⌋:=∅ →
                        snd r ⇐ ex2 ⌊ ⛽ ⌋:=∅
      XBFMatch      : ∀{⛽ ⛽↓ E r rules ex} →
                        ⛽ ⛽⇓ ⛽↓ →
                        ex ≠ ¿¿ →
                        -- for every constructor, one of three failures must occur
                        (∀{c-j x-j e-j} →
                           (c-j , |C x-j => e-j) ∈ rules →
                             -- fails to backpropagate the constructor to the scrutinee
                             r ⇐ C[ c-j ] ¿¿ ⌊ ⛽ ⌋:=∅
                                  {- OR -} ∨ Σ[ k1 ∈ constraints ] (
                             -- fails evaluation (2nd line)
                             r ⇐ C[ c-j ] ¿¿ ⌊ ⛽ ⌋:= k1 ∧
                             (E ,, (x-j , C⁻[ c-j ] r)) ⊢ e-j ⌊ ⛽↓ ⌋⇒∅)
                                  {- OR -} ∨ Σ[ k1 ∈ constraints ] Σ[ k2 ∈ constraints ] Σ[ r-j ∈ result ] (
                             -- the (successfully) eval'd result fails backpropagation (3rd line)
                             r ⇐ C[ c-j ] ¿¿ ⌊ ⛽ ⌋:= k1 ∧
                             (E ,, (x-j , C⁻[ c-j ] r)) ⊢ e-j ⌊ ⛽↓ ⌋⇒ r-j ⊣ k2 ∧
                             r-j ⇐ ex ⌊ ⛽↓ ⌋:=∅)) →
                        [ E ]case r of⦃· rules ·⦄ ⇐ ex ⌊ ⛽ ⌋:=∅
      XBFUnwrapCtor : ∀{⛽ c r ex} →
                        ex ≠ ¿¿ →
                        r ⇐ C[ c ] ex ⌊ ⛽ ⌋:=∅ →
                        (C⁻[ c ] r) ⇐ ex ⌊ ⛽ ⌋:=∅

    -- Generic evaluation failure - this goes through if evaluation would fail due to unsatisfiablility
    -- of a some constraint collection or backpropagation attempt that occurs during evaluation,
    -- and it may go through if evaluation diverges.
    -- But this judgment cannot be satisfied if evaluation converges and all constraints are valid.
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
      EFAsrt       : ∀{E ⛽ e1 r1 k1 e2 r2 k2} →
                       E ⊢ e1 ⌊ ⛽ ⌋⇒ r1 ⊣ k1 →
                       E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ k2 →
                       Constraints⦃ r1 , r2 ⦄⌊ ⛽ ⌋:=∅ →
                       E ⊢ PBE:assert e1 e2 ⌊ ⛽ ⌋⇒∅

  -- Evaluation failure - the ordinary version with no beta reduction counting or limit
  _⊢_⇒∅ : env → exp → Set
  E ⊢ e ⇒∅ = E ⊢ e ⌊ ∞ ⌋⇒∅

  -- TODO theorems for everything below, including resumption, synthesis, solve, satisfaction, consistency, Group, and Filter

  -- resumption

  hole-fillings = exp ctx

  -- resumption
  data _⊢_⇨_:=_ : hole-fillings → result → result → constraints → Set where
    RFix           : ∀{H E f x e r} →
                       r == [ E ]fix f ⦇·λ x => e ·⦈ →
                       H ⊢ r ⇨ r := []
    RHoleFill      : ∀{H E u r e k} →
                       (u , e) ∈ H →
                       E ⊢ e ⇒ r ⊣ k →
                       H ⊢ [ E ]??[ u ] ⇨ r := k
    RHoleUnf       : ∀{H E u} →
                       u # H →
                       H ⊢ [ E ]??[ u ] ⇨ [ E ]??[ u ] := []
    RUnit          : ∀{H} → H ⊢ ⟨⟩ ⇨ ⟨⟩ := []
    RPair          : ∀{H r1 r2 r1' r2' k1 k2} →
                       H ⊢ r1 ⇨ r1' := k1 →
                       H ⊢ r2 ⇨ r2' := k2 →
                       H ⊢ ⟨ r1 , r2 ⟩ ⇨ ⟨ r1' , r2' ⟩ := k1 ++ k2
    RCtor          : ∀{H c r r' k} →
                       H ⊢ r ⇨ r' := k →
                       H ⊢ C[ c ] r ⇨ C[ c ] r' := k
    RUnwrapCtor    : ∀{H c r rc rc' k k'} →
                       H ⊢ r ⇨ C[ c ] rc := k →
                       H ⊢ rc ⇨ rc' := k' →
                       H ⊢ C⁻[ c ] r ⇨ rc' := k ++ k'
    RUnwrapCtorUnf : ∀{H c r r' k} →
                       H ⊢ r ⇨ r' := k →
                       (∀{c r''} → r' ≠ (C[ c ] r'')) →
                       H ⊢ C⁻[ c ] r ⇨ C⁻[ c ] r' := k
    RApp           : ∀{H rf rarg r' Ef f x ef rf' rarg' kf karg kef} →
                       H ⊢ rf ⇨ rf' := kf →
                       rf' == [ Ef ]fix f ⦇·λ x => ef ·⦈ →
                       H ⊢ rarg ⇨ rarg' := karg →
                       (Ef ,, (f , rf) ,, (x , rarg)) ⊢ ef ⇒ r' ⊣ kef →
                       H ⊢ rf ∘ rarg ⇨ r' := kf ++ karg ++ kef
    RAppUnf        : ∀{H rf rarg rf' rarg' kf karg} →
                       H ⊢ rf ⇨ rf' := kf →
                       (∀{E f x e} → rf' ≠ [ E ]fix f ⦇·λ x => e ·⦈) →
                       H ⊢ rarg ⇨ rarg' := karg →
                       H ⊢ rf ∘ rarg ⇨ rf' ∘ rarg' := kf ++ karg
    RFst           : ∀{H r r1 r2 k} →
                       H ⊢ r ⇨ ⟨ r1 , r2 ⟩ := k →
                       H ⊢ fst r ⇨ r1 := k
    RFstUnf        : ∀{H r r' k} →
                       H ⊢ r ⇨ r' := k →
                       (∀{r1 r2} → r' ≠ ⟨ r1 , r2 ⟩) →
                       H ⊢ fst r ⇨ fst r' := k
    RSnd           : ∀{H r r1 r2 k} →
                       H ⊢ r ⇨ ⟨ r1 , r2 ⟩ := k →
                       H ⊢ snd r ⇨ r2 := k
    RSndUnf        : ∀{H r r' k} →
                       H ⊢ r ⇨ r' := k →
                       (∀{r1 r2} → r' ≠ ⟨ r1 , r2 ⟩) →
                       H ⊢ snd r ⇨ snd r' := k
    RMatch         : ∀{H E r rules c xc ec r' rc kc k} →
                       (c , |C xc => ec) ∈ rules →
                       H ⊢ r ⇨ (C[ c ] r') := kc →
                       (E ,, (xc , r')) ⊢ ec ⇒ rc ⊣ k →
                       H ⊢ [ E ]case r of⦃· rules ·⦄ ⇨ rc := kc ++ k
    RMatchUnf      : ∀{H E r rules r' k} →
                       H ⊢ r ⇨ r' := k →
                       (∀{c r''} → r' ≠ (C[ c ] r'')) →
                       H ⊢ [ E ]case r of⦃· rules ·⦄ ⇨ [ E ]case r' of⦃· rules ·⦄ := k

  -- type checking for hole fillings
  data _,_⊢ₕ_ : hctx → denv → hole-fillings → Set where
    TANil         : ∀{Δ Σ'} → Δ , Σ' ⊢ₕ ∅
    TAHoleFilling : ∀{Δ Σ' H u e Γ τ} →
                      (u , Γ , τ) ∈ Δ →
                      Δ , Σ' ⊢ₕ H →
                      Δ , Σ' , Γ ⊢ e :: τ →
                      Δ , Σ' ⊢ₕ (H ,, (u , e))

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

  -- TODO proof that backprop generalizes satisfaction stuff?

  -- TODO theorem that synthesized expressions evaluate completely with no constraints
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

  -- Live World Consistency
  -- TODO should only take undets?
  data _⊨_:=_ : worlds → exp → constraints → Set where
    SEmpty : ∀{e} → [] ⊨ e := []
    SWorld : ∀{W E ex e r k1 k2} →
               W ⊨ e := k1 →
               E ⊢ e ⇒ r ⊣ [] →
               r ⇐ ex := k2 →
               ((E , ex) :: W) ⊨ e := k1 ++ k2

  -- synthesis

  mutual
    -- synthesis by refinement
    data _,_,_,_⊢??[_]::_⇝_:=_,_ : hctx → denv → tctx → worlds → Nat → typ → exp → constraints → hctx → Set where
      IRUnit : ∀{Δ Σ' Γ W u} → Δ , Σ' , Γ , W ⊢??[ u ]:: ⟨⟩ ⇝ ⟨⟩ := [] , ∅
      -- TODO maybe package up ex1s and ex2s into a W'
      IRPair : ∀{Δ Σ' Γ W u Es ex1s ex2s τ1 τ2 u1 u2 k1 k2 Δ'} →
                 ∥ Es ∥ == ∥ ex1s ∥ →
                 ∥ Es ∥ == ∥ ex2s ∥ →
                 Filter W :=> zip Es (map (λ {(ex1 , ex2) → ⟨ ex1 , ex2 ⟩}) (zip ex1s ex2s)) →
                 u1 # Δ →
                 u1 ≠ u →
                 u2 # Δ →
                 u2 ≠ u →
                 u1 ≠ u2 →
                 Δ' == (■ (u1 , Γ , τ1) ,, (u2 , Γ , τ2)) →
                 k1 == map (λ {(E , ex) → [ E ]??[ u1 ] , ex}) (zip Es ex1s) →
                 k2 == map (λ {(E , ex) → [ E ]??[ u2 ] , ex}) (zip Es ex2s) →
                 Δ , Σ' , Γ , W ⊢??[ u ]:: ⟨ τ1 × τ2 ⟩ ⇝ ⟨ ??[ u1 ] , ??[ u2 ] ⟩ := k1 ++ k2 , Δ'
      IRCtor : ∀{Δ Σ' Γ W u d cctx c τ u' k Δ'} {W' : List (env ∧ ex)} →
                 (d , cctx) ∈ π1 Σ' →
                 (c , τ) ∈ cctx →
                 Filter W :=> map (λ {(E , ex) → E , C[ c ] ex}) W' →
                 u' # Δ →
                 u' ≠ u →
                 Δ' == ■ (u' , Γ , τ) →
                 k == map (λ {(E , ex) → [ E ]??[ u' ] , ex}) W' →
                 Δ , Σ' , Γ , W ⊢??[ u ]:: D[ d ] ⇝ C[ c ] ??[ u' ] := k , Δ'
      IRFix  : ∀{Δ Σ' Γ W u τ1 τ2 f x u' k Δ'} {W' : List (env ∧ result ∧ ex)} →
                 Filter W :=> map (λ {(E , r , ex) → E , r ↦ ex}) W' →
                 u' # Δ →
                 u' ≠ u →
                 Δ' == ■ (u' , (Γ ,, (f , τ1 ==> τ2) ,, (x , τ1)) , τ2) →
                 k == map (λ {(E , r , ex) → [ E ,, (f , [ E ]fix f ⦇·λ x => ??[ u' ] ·⦈) ,, (x , r) ]??[ u' ] , ex}) W' →
                 Δ , Σ' , Γ , W ⊢??[ u ]:: τ1 ==> τ2 ⇝ fix f ⦇·λ x => ??[ u' ] ·⦈ := k , Δ'
      {- TODO
      IRMatch : ∀{Δ Σ' Γ W u Wf Wf-evald Wf-ctx τ e rules d cctx x k-ctx} →
                  Δ , Σ' , Γ , W ⊢??[ u ]:: τ ⇝ case e of⦃· rules ·⦄ := foldl _++_ [] (ctx⇒values k-ctx) , {!!}
      IRMatch : ∀{Δ Σ' Γ W Wf Wf-evald Wf-ctx τ e rules d cctx x k-ctx} →
                  (∀{c} → dom k-ctx c → dom rules c) →
                  (∀{c} → dom rules c → dom k-ctx c) →
                  -- choose a datatype
                  (d , cctx) ∈ π1 Σ' →
                  (∀{c} → dom cctx c → dom rules c) →
                  (∀{c} → dom rules c → dom cctx c) →
                  -- choose one fresh variable name that will be used for all cases
                  x # Γ →
                  (∀{c rule} → (c , rule) ∈ rules → rule.parm rule == x) →
                  -- synthesize a scrutinee
                  Δ , Σ' , Γ ⊢ D[ d ] ⇝ e →
                  -- For each world of Filter W, the corresponding element in Wf-evald is a pair
                  -- of the constructor name and result that the scrutinee would evaluate
                  -- to in that world.
                  Filter W :=> Wf →
                  ∥ Wf ∥ == ∥ Wf-evald ∥ →
                  (∀{i E-i ex-i c-i r-i} →
                     Wf       ⟦ i ⟧ == Some (E-i , ex-i) →
                     Wf-evald ⟦ i ⟧ == Some (c-i , r-i) →
                     E-i ⊢ e ⇒ C[ c-i ] r-i ⊣ []) →
                  -- For each c in the domain of cctx, Wf-ctx maps to a list of extended worlds,
                  -- where each extended world has the specified example, but an env where the
                  -- branch variable x is assosiated with the value that the scrutinee evaluates
                  -- to under the original env.
                  Wf-ctx ==
                    (ctxmap (λ _ → []) cctx)
                      ∪
                    (list⇒ctx (map (λ {((E , ex) , c , r) → c , (E ,, (x , r)) , ex}) (zip Wf Wf-evald))) →
                  -- Each rule's branch expression must synthesize under the aforementioned
                  -- extended worlds.
                  (∀{c ec τc Wc kc} →
                     (c , |C x => ec) ∈ rules →
                     (c , τc) ∈ cctx →
                     (c , Wc) ∈ Wf-ctx →
                     (c , kc) ∈ k-ctx →
                     Δ , Σ' , (Γ ,, (x , τc)) , Wc ⊢ τ ⇝ ec := kc) →
                  Δ , Σ' , Γ , W ⊢ τ ⇝ case e of⦃· rules ·⦄ := foldl _++_ [] (ctx⇒values k-ctx)
                  -}
      IRGuess : ∀{Δ Σ' Γ W u τ e k Δ'} →
                  Δ , Σ' , Γ ⊢ τ ⇝ e := Δ' →
                  W ⊨ e := k →
                  Δ , Σ' , Γ , W ⊢??[ u ]:: τ ⇝ e := k , Δ'
      IRHole  : ∀{Δ Σ' Γ W u τ} →
                  W ≠ [] →
                  Filter W :=> [] →
                  Δ , Σ' , Γ , W ⊢??[ u ]:: τ ⇝ ??[ u ] := [] , ∅

    -- synthesis by guess
    data _,_,_⊢_⇝_:=_ : hctx → denv → tctx → typ → exp → hctx → Set where
      EGVar : ∀{Δ Σ' Γ τ x} →
                (x , τ) ∈ Γ →
                Δ , Σ' , Γ ⊢ τ ⇝ X[ x ] := ∅
      EGApp : ∀{Δ Σ' Γ τ1 τ2 e1 e2 u' k Δ1 Δ2} →
                -- TODO define ##
                (∀{u} → dom Δ1 u → u # Δ2) →
                Δ , Σ' , Γ ⊢ τ1 ==> τ2 ⇝ e1 := Δ1 →
                u' # Δ →
                -- TODO prove k is always []
                Δ , Σ' , Γ , [] ⊢??[ u' ]:: τ1 ⇝ e2 := k , Δ2 →
                Δ , Σ' , Γ ⊢ τ2 ⇝ e1 ∘ e2 := (Δ1 ∪ Δ2)
      EGFst : ∀{Δ Σ' Γ τ1 τ2 e Δ'} →
                Δ , Σ' , Γ ⊢ ⟨ τ1 × τ2 ⟩ ⇝ e := Δ' →
                Δ , Σ' , Γ ⊢ τ1 ⇝ fst e := Δ'
      EGSnd : ∀{Δ Σ' Γ τ1 τ2 e Δ'} →
                Δ , Σ' , Γ ⊢ ⟨ τ1 × τ2 ⟩ ⇝ e := Δ' →
                Δ , Σ' , Γ ⊢ τ2 ⇝ snd e := Δ'

  -- Example Satisfaction for results
  data _,_·⊨_ : hole-fillings → result → ex → Set where
    XSUnit  : ∀{H} → H , ⟨⟩ ·⊨ ⟨⟩
    XSPair  : ∀{H r r1 r2 ex1 ex2} →
                H ⊢ r ⇨ ⟨ r1 , r2 ⟩ := [] →
                H , r1 ·⊨ ex1 →
                H , r2 ·⊨ ex2 →
                H , r ·⊨ ⟨ ex1 , ex2 ⟩
    XSCtor  : ∀{H r r' c ex} →
                H ⊢ r ⇨ C[ c ] r' := [] →
                H , r' ·⊨ ex →
                H , r ·⊨ (C[ c ] ex)
    XSInOut : ∀{H r1 r2 v ex} →
                H ⊢ r1 ∘ r2 ⇨ v := [] →
                v value →
                H , v ·⊨ ex →
                H , r1 ·⊨ (r2 ↦ ex)
    XSNone  : ∀{H r} → H , r ·⊨ ¿¿

  -- Constraint Satisfaction for results
  data _⊨_ : hole-fillings → constraints → Set where
    CSEmpty      : ∀{H} → H ⊨ []
    CSConstraint : ∀{H k r ex} →
                     H ⊨ k →
                     H , r ·⊨ ex →
                     H ⊨ ((r , ex) :: k)

  -- Constraint satisfaction for exps
  data _,_:⊨_ : hole-fillings → exp → worlds → Set where
    CSEmpty      : ∀{H e} → H , e :⊨ []
    CSConstraint : ∀{H e E ex W r} →
                     H , e :⊨ W →
                     E ⊢ e ⇒ r ⊣ [] →
                     H , r ·⊨ ex →
                     H , e :⊨ ((E , ex) :: W)

  Split : constraints → List (Nat ∧ world) ∧ constraints
  Split [] = ([] , [])
  Split (([ E ]??[ u ] , ex) :: r)
    with Split r
  ...  | k-holes , k-undets = (u , E , ex) :: k-holes , k-undets
  Split (h :: r) -- TODO the catch-all h isn't going to play nicely with proofs
    with Split r
  ...  | k-holes , k-undets = k-holes , h :: k-undets

  Group : List (Nat ∧ world) → worlds ctx
  Group = list⇒ctx

  {- TODO fix after info from Ravi }
  data _,_⊢IterSolve_:=_,_ : hctx → denv → constraints → hole-fillings → hctx → Set where
    ISRec  : ∀{Δ Σ' k k-holes k-undets g ek-ctx k' h} →
               Split k == k-holes , k-undets →
               Group k-holes == g →
               (∀{u} → dom g u → dom Δ u) →
               (∀{u} → dom g u → dom ek-ctx u) →
               (∀{u} → dom ek-ctx u → dom g u) →
               (∀{u Wu Γu τu eu ku} →
                  (u , Wu) ∈ g →
                  (u , Γu , τu) ∈ Δ →
                  (u , eu , ku) ∈ ek-ctx →
                  Δ , Σ' , Γu , Wu ⊢ τu ⇝ eu := ku) →
               k' == foldl _++_ k (map π2 (ctx⇒values ek-ctx)) →
               Δ , Σ' ⊢IterSolve k' := h →
               Δ , Σ' ⊢IterSolve k := h , Δ''
    ISTerm : ∀{Δ Σ' k k-holes k-undets g h} →
               Split k == k-holes , k-undets →
               Group k-holes == g →
               (∀{u} → dom g u → dom Δ u) →
               (∀{u} → dom g u → dom h u) →
               (∀{u} → dom h u → dom g u) →
               (∀{u Wu Γu τu eu} →
                  (u , Wu) ∈ g →
                  (u , Γu , τu) ∈ Δ →
                  (u , eu) ∈ h →
                  Δ , Σ' , Γu , Wu ⊢ τu ⇝ eu := []) →
               Δ , Σ' ⊢IterSolve k := h
               -}

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
