open import Nat
open import Prelude
open import List
open import contexts
open import unions

module core where
  -- types
  data typ : Set where
    _==>_ : typ → typ → typ
    ⟨⟩    : typ
    ⟨_×_⟩ : typ → typ → typ
    D[_]  : Nat → typ

  -- arrow type constructors bind very tightly
  infixr 25  _==>_

  -- type contexts, hole contexts, and datatype environments
  tctx = typ ctx
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
    VTUnit : ∀{Σ'} → Σ' ⊢ ⟨⟩ ::ⱽ ⟨⟩
    VTPair : ∀{Σ' v1 v2 τ1 τ2} →
               Σ' ⊢ v1 ::ⱽ τ1 →
               Σ' ⊢ v2 ::ⱽ τ2 →
               Σ' ⊢ ⟨ v1 , v2 ⟩ ::ⱽ ⟨ τ1 × τ2 ⟩
    VTCtor : ∀{Σ' d cctx c v τ} →
               (d , cctx) ∈ π1 Σ' →
               (c , τ) ∈ cctx →
               Σ' ⊢ v ::ⱽ τ →
               Σ' ⊢ C[ c ] v ::ⱽ D[ d ]

  -- example typing
  data _,_⊢_:·_ : hctx → denv → ex → typ → Set where
    XTUnit  : ∀{Δ Σ'} → Δ , Σ' ⊢ ⟨⟩ :· ⟨⟩
    XTPair  : ∀{Δ Σ' ex1 ex2 τ1 τ2} →
                Δ , Σ' ⊢ ex1 :· τ1 →
                Δ , Σ' ⊢ ex2 :· τ2 →
                Δ , Σ' ⊢ ⟨ ex1 , ex2 ⟩ :· ⟨ τ1 × τ2 ⟩
    XTCtor  : ∀{Δ Σ' d cctx c ex τ} →
                (d , cctx) ∈ π1 Σ' →
                (c , τ) ∈ cctx →
                Δ , Σ' ⊢ ex :· τ →
                Δ , Σ' ⊢ C[ c ] ex :· D[ d ]
    XTTop   : ∀{Δ Σ' τ} → Δ , Σ' ⊢ ¿¿ :· τ
    XTInOut : ∀{Δ Σ' v ex τ1 τ2} →
                Σ' ⊢ v ::ⱽ τ1 →
                Δ , Σ' ⊢ ex :· τ2 →
                Δ , Σ' ⊢ v ↦ ex :· τ1 ==> τ2

  -- the two possible prj indices
  data prj-idx : Set where
    P1 : prj-idx
    P2 : prj-idx

  prj : {A : Set} → prj-idx → A → A → A
  prj P1 a1 a2 = a1
  prj P2 a1 a2 = a2

  mutual
    record rule : Set where
      inductive
      constructor |C_=>_
      field
        parm   : Nat
        branch : exp

    -- Expressions
    data exp : Set where
      fix_⦇·λ_=>_·⦈ : Nat → Nat → exp → exp
      _∘_           : exp → exp → exp
      X[_]          : Nat → exp
      ⟨⟩            : exp
      ⟨_,_⟩         : exp → exp → exp
      prj[_]_       : prj-idx → exp → exp
      C[_]_         : Nat → exp → exp
      case_of⦃·_·⦄ : exp → rule ctx → exp
      ??[_]         : Nat → exp
      PBE:assert    : exp → exp → exp

  -- u is fresh in e
  data hole-name-new : (e : exp) → (u : Nat) → Set where
    HNNFix  : ∀{x f e u} → hole-name-new e u → hole-name-new (fix f ⦇·λ x => e ·⦈) u
    HNNVar  : ∀{x u} → hole-name-new (X[ x ]) u
    HNNAp   : ∀{e1 e2 u} → hole-name-new e1 u → hole-name-new e2 u → hole-name-new (e1 ∘ e2) u
    HNNUnit : ∀{u} → hole-name-new ⟨⟩ u
    HNNPair : ∀{e1 e2 u} → hole-name-new e1 u → hole-name-new e2 u → hole-name-new ⟨ e1 , e2 ⟩ u
    HNNPrj  : ∀{e i u} → hole-name-new e u → hole-name-new (prj[ i ] e) u
    HNNCtor : ∀{c e u} → hole-name-new e u → hole-name-new (C[ c ] e) u
    HNNCase : ∀{e rules u} →
                hole-name-new e u →
                (∀{c rule} → (c , rule) ∈ rules → hole-name-new (rule.branch rule) u) →
                hole-name-new (case e of⦃· rules ·⦄) u
    HNNHole : ∀{u' u} → u' ≠ u → hole-name-new (??[ u' ]) u
    HNNAsrt : ∀{e1 e2 u} → hole-name-new e1 u → hole-name-new e2 u → hole-name-new (PBE:assert e1 e2) u

  -- e1 and e2 do not have any hole names in common
  data holes-disjoint : (e1 : exp) → (e2 : exp) → Set where
    HDFix  : ∀{x f e e'} → holes-disjoint e e' → holes-disjoint (fix f ⦇·λ x => e ·⦈) e'
    HDVar  : ∀{x e'} → holes-disjoint (X[ x ]) e'
    HDAp   : ∀{e1 e2 e'} → holes-disjoint e1 e' → holes-disjoint e2 e' → holes-disjoint (e1 ∘ e2) e'
    HDUnit : ∀{e'} → holes-disjoint ⟨⟩ e'
    HDPair : ∀{e1 e2 e'} → holes-disjoint e1 e' → holes-disjoint e2 e' → holes-disjoint ⟨ e1 , e2 ⟩ e'
    HDPrj  : ∀{i e e'} → holes-disjoint e e' → holes-disjoint (prj[ i ] e) e'
    HDCtor : ∀{c e e'} → holes-disjoint e e' → holes-disjoint (C[ c ] e) e'
    HDCase : ∀{e rules e'} →
               holes-disjoint e e' →
               (∀{c rule} → (c , rule) ∈ rules → holes-disjoint (rule.branch rule) e') →
               holes-disjoint (case e of⦃· rules ·⦄) e'
    HDHole : ∀{u e'} → hole-name-new e' u → holes-disjoint (??[ u ]) e'
    HDAsrt : ∀{e1 e2 e'} → holes-disjoint e1 e' → holes-disjoint e2 e' → holes-disjoint (PBE:assert e1 e2) e'

  -- e ecomplete iff e contains no holes
  data _ecomplete : exp → Set where
    ECFix  : ∀{f x e} → e ecomplete → fix f ⦇·λ x => e ·⦈ ecomplete
    ECVar  : ∀{x} → X[ x ] ecomplete
    ECAp   : ∀{e1 e2} → e1 ecomplete → e2 ecomplete → (e1 ∘ e2) ecomplete
    ECUnit : ⟨⟩ ecomplete
    ECPair : ∀{e1 e2} → e1 ecomplete → e2 ecomplete → ⟨ e1 , e2 ⟩ ecomplete
    ECPrj  : ∀{i e} → e ecomplete → (prj[ i ] e) ecomplete
    ECCtor : ∀{c e} → e ecomplete → (C[ c ] e) ecomplete
    ECCase : ∀{e rules} →
               e ecomplete →
               (∀{c rule} → (c , rule) ∈ rules → (rule.branch rule) ecomplete) →
               case e of⦃· rules ·⦄ ecomplete
    ECAsrt : ∀{e1 e2} → e1 ecomplete → e2 ecomplete → (PBE:assert e1 e2) ecomplete

  -- type assignment for expressions
  data _,_,_⊢_::_ : hctx → denv → tctx → exp → typ → Set where
    TFix  : ∀{Δ Σ' Γ f x e τ1 τ2} →
              Δ , Σ' , (Γ ,, (f , τ1 ==> τ2) ,, (x , τ1)) ⊢ e :: τ2 →
              Δ , Σ' , Γ ⊢ fix f ⦇·λ x => e ·⦈ :: τ1 ==> τ2
    TVar  : ∀{Δ Σ' Γ x τ} → (x , τ) ∈ Γ → Δ , Σ' , Γ ⊢ X[ x ] :: τ
    THole : ∀{Δ Σ' Γ u τ} → (u , (Γ , τ)) ∈ Δ → Δ , Σ' , Γ ⊢ ??[ u ] :: τ
    TUnit : ∀{Δ Σ' Γ} → Δ , Σ' , Γ ⊢ ⟨⟩ :: ⟨⟩
    TPair : ∀{Δ Σ' Γ e1 e2 τ1 τ2} →
              holes-disjoint e1 e2 →
              Δ , Σ' , Γ ⊢ e1 :: τ1 →
              Δ , Σ' , Γ ⊢ e2 :: τ2 →
              Δ , Σ' , Γ ⊢ ⟨ e1 , e2 ⟩ :: ⟨ τ1 × τ2 ⟩
    TCtor : ∀{Δ Σ' Γ d cctx c e τ} →
              (d , cctx) ∈ π1 Σ' →
              (c , τ) ∈ cctx →
              Δ , Σ' , Γ ⊢ e :: τ →
              Δ , Σ' , Γ ⊢ C[ c ] e :: D[ d ]
    TApp  : ∀{Δ Σ' Γ f arg τ1 τ2} →
              holes-disjoint f arg →
              Δ , Σ' , Γ ⊢ f :: τ1 ==> τ2 →
              Δ , Σ' , Γ ⊢ arg :: τ1 →
              Δ , Σ' , Γ ⊢ f ∘ arg :: τ2
    TPrj  : ∀{Δ Σ' Γ i e τ1 τ2} →
              Δ , Σ' , Γ ⊢ e :: ⟨ τ1 × τ2 ⟩ →
              Δ , Σ' , Γ ⊢ prj[ i ] e :: prj i τ1 τ2
    TCase : ∀{Δ Σ' Γ d cctx e rules τ} →
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
    TAssert : ∀{Δ Σ' Γ e1 e2 τ} →
                holes-disjoint e1 e2 →
                Δ , Σ' , Γ ⊢ e1 :: τ →
                Δ , Σ' , Γ ⊢ e2 :: τ →
                Δ , Σ' , Γ ⊢ PBE:assert e1 e2 :: ⟨⟩

  mutual
    env : Set
    env = result ctx

    -- results - evaluation takes expressions to results, but results aren't necessarily final
    data result : Set where
      [_]fix_⦇·λ_=>_·⦈ : env → Nat → Nat → exp → result
      ⟨⟩               : result
      ⟨_,_⟩            : result → result → result
      C[_]_            : Nat → result → result
      [_]??[_]         : env → Nat → result
      _∘_              : result → result → result
      prj[_]_          : prj-idx → result → result
      [_]case_of⦃·_·⦄ : env → result → rule ctx → result
      C⁻¹[_]_           : Nat → result → result

  mutual
    data _env-final : env → Set where
      EFNone : ∅ env-final
      EFInd  : ∀{E x r} → E env-final → r final → (E ,, (x , r)) env-final

    -- final results are those that cannot be evaluated further
    data _final : result → Set where
      FDet   : ∀{r} → r det → r final
      FIndet : ∀{r} → r indet → r final

    -- final results that can be eliminated (or in the case of ⟨⟩, that don't need to be)
    data _det : result → Set where
      DFix  : ∀{E f x e} → E env-final → [ E ]fix f ⦇·λ x => e ·⦈ det
      DUnit : ⟨⟩ det
      DPair : ∀{r1 r2} → r1 final → r2 final → ⟨ r1 , r2 ⟩ det
      DCtor : ∀{c r} → r final → (C[ c ] r) det

    -- indeterminate results are incomplete and cannot be further reduced except by resumption
    data _indet : result → Set where
      IDHole : ∀{E u} → E env-final → [ E ]??[ u ] indet
      IDApp  : ∀{r1 r2} → r1 indet → r2 final → (r1 ∘ r2) indet
      IDPrj  : ∀{i r} → r indet → (prj[ i ] r) indet
      IDCase : ∀{E r rules} → E env-final → r indet → [ E ]case r of⦃· rules ·⦄ indet

  mutual
    -- type assignment for environments
    data _,_,_⊢_ : hctx → denv → tctx → env → Set where
      EnvId  : ∀{Δ Σ'} → Δ , Σ' , ∅ ⊢ ∅
      EnvInd : ∀{Δ Σ' Γ E x τx rx} →
                 Δ , Σ' , Γ ⊢ E →
                 Δ , Σ' ⊢ rx ·: τx →
                 Δ , Σ' , (Γ ,, (x , τx)) ⊢ (E ,, (x , rx))

    -- type assignment for results
    data _,_⊢_·:_ : hctx → denv → result → typ → Set where
      RTFix        : ∀{Δ Σ' Γ E f x e τ} →
                       Δ , Σ' , Γ ⊢ E →
                       Δ , Σ' , Γ ⊢ fix f ⦇·λ x => e ·⦈ :: τ →
                       Δ , Σ' ⊢ [ E ]fix f ⦇·λ x => e ·⦈ ·: τ
      RTHole       : ∀{Δ Σ' Γ E u τ} →
                       (u , (Γ , τ)) ∈ Δ →
                       Δ , Σ' , Γ ⊢ E →
                       Δ , Σ' ⊢ [ E ]??[ u ] ·: τ
      RTUnit       : ∀{Δ Σ'} → Δ , Σ' ⊢ ⟨⟩ ·: ⟨⟩
      RTPair       : ∀{Δ Σ' r1 r2 τ1 τ2} →
                       Δ , Σ' ⊢ r1 ·: τ1 →
                       Δ , Σ' ⊢ r2 ·: τ2 →
                       Δ , Σ' ⊢ ⟨ r1 , r2 ⟩ ·: ⟨ τ1 × τ2 ⟩
      RTCtor       : ∀{Δ Σ' d cctx c r τ} →
                       (d , cctx) ∈ π1 Σ' →
                       (c , τ) ∈ cctx →
                       Δ , Σ' ⊢ r ·: τ →
                       Δ , Σ' ⊢ C[ c ] r ·: D[ d ]
      RTApp        : ∀{Δ Σ' f arg τ1 τ2} →
                       Δ , Σ' ⊢ f ·: τ1 ==> τ2 →
                       Δ , Σ' ⊢ arg ·: τ1 →
                       Δ , Σ' ⊢ f ∘ arg ·: τ2
      RTPrj        : ∀{Δ Σ' i r τ1 τ2} →
                       Δ , Σ' ⊢ r ·: ⟨ τ1 × τ2 ⟩ →
                       Δ , Σ' ⊢ prj[ i ] r ·: prj i τ1 τ2
      RTCase       : ∀{Δ Σ' Γ E d cctx r rules τ} →
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
      RTUnwrapCtor : ∀{Δ Σ' d cctx c r τ} →
                       (d , cctx) ∈ π1 Σ' →
                       (c , τ) ∈ cctx →
                       Δ , Σ' ⊢ r ·: D[ d ] →
                       Δ , Σ' ⊢ C⁻¹[ c ] r ·: τ

  excon         = env ∧ ex
  excons        = List excon
  assertions    = List (result ∧ val)
  hole-fillings = exp ctx
  constraints   = hole-fillings ∧ excons ctx

  record goal : Set where
    inductive
    constructor _⊢??[_]:_⊨_
    field
      g-tctx   : tctx
      g-id     : Nat
      g-typ    : typ
      g-excons : excons

  goals = List goal

  -- value-to-example coercion
  ⌊_⌋ : val → ex
  ⌊ ⟨⟩ ⌋ = ⟨⟩
  ⌊ ⟨ v1 , v2 ⟩ ⌋ = ⟨ ⌊ v1 ⌋ , ⌊ v2 ⌋ ⟩
  ⌊ C[ c ] v ⌋ = C[ c ] ⌊ v ⌋

  -- result-to-value coercion
  data ⌈_⌉:=_ : result → val → Set where
    CoerceUnit : ⌈ ⟨⟩ ⌉:= ⟨⟩
    CoercePair : ∀{r1 r2 v1 v2} →
                   ⌈ r1 ⌉:= v1 →
                   ⌈ r2 ⌉:= v2 →
                   ⌈ ⟨ r1 , r2 ⟩ ⌉:= ⟨ v1 , v2 ⟩
    CoerceCtor : ∀{c r v} →
                   ⌈ r ⌉:= v →
                   ⌈ C[ c ] r ⌉:= C[ c ] v

  -- excons typing
  data _,_⊢_::ˣ_,_ : hctx → denv → excons → tctx → typ → Set where
    TXNil : ∀{Δ Σ' Γ τ} → Δ , Σ' ⊢ [] ::ˣ Γ , τ
    TXInd : ∀{Δ Σ' X E ex Γ τ} →
              Δ , Σ' ⊢ X ::ˣ Γ , τ →
              Δ , Σ' , Γ ⊢ E →
              Δ , Σ' ⊢ ex :· τ →
              Δ , Σ' ⊢ ((E , ex) :: X) ::ˣ Γ , τ

  -- type assignment for hole fillings
  data _,_⊢ᴴ_ : hctx → denv → hole-fillings → Set where
    TFNil : ∀{Δ Σ'} → Δ , Σ' ⊢ᴴ ∅
    TFInd : ∀{Δ Σ' F u Γ τ e} →
              (u , Γ , τ) ∈ Δ →
              Δ , Σ' ⊢ᴴ F →
              Δ , Σ' , Γ ⊢ e :: τ →
              Δ , Σ' ⊢ᴴ (F ,, (u , e))

  {- TODO - we have to decide between this version and the one prior
  _,_⊢ₕ_ : hctx → denv → hole-fillings → Set
  Δ , Σ' ⊢ₕ F = ∀{u e} →
                  (u , e) ∈ F →
                  Σ[ Γ ∈ tctx ] Σ[ τ ∈ typ ] (
                     (u , Γ , τ) ∈ Δ ∧
                     Δ , Σ' , Γ ⊢ e :: τ)
  -}

  -- these are used to determine the "order" in which result consistency rules are checked
  not-both-pair : (r r' : result) → Set
  not-both-pair r r' = (∀{r1 r2} → r ≠ ⟨ r1 , r2 ⟩)  ∨ (∀{r1 r2} → r' ≠ ⟨ r1 , r2 ⟩)
  not-both-ctor : (r r' : result) → Set
  not-both-ctor r r' = (∀{c r''} → r ≠ (C[ c ] r'')) ∨ (∀{c r''} → r' ≠ (C[ c ] r''))

  -- result consistency
  data _≡⌊_⌋_ : result → assertions → result → Set where
    RCRefl    : ∀{r} → r ≡⌊ [] ⌋ r
    RCPair    : ∀{r1 r2 r'1 r'2 A1 A2} →
                  (_==_ {A = result} ⟨ r1 , r2 ⟩ ⟨ r'1 , r'2 ⟩ → ⊥) →
                  r1 ≡⌊ A1 ⌋ r'1 →
                  r2 ≡⌊ A2 ⌋ r'2 →
                  ⟨ r1 , r2 ⟩ ≡⌊ A1 ++ A2 ⌋ ⟨ r'1 , r'2 ⟩
    RCCtor    : ∀{c r r' A} →
                  (_==_ {A = result} (C[ c ] r) (C[ c ] r') → ⊥) →
                  r ≡⌊ A ⌋ r' →
                  (C[ c ] r) ≡⌊ A ⌋ (C[ c ] r')
    RCAssert1 : ∀{r1 r2 v2 A} →
                  r1 ≠ r2 →
                  not-both-pair r1 r2 →
                  not-both-ctor r1 r2 →
                  ⌈ r2 ⌉:= v2 →
                  A == (r1 , v2) :: [] →
                  r1 ≡⌊ A ⌋ r2
    RCAssert2 : ∀{r1 r2 v1 A} →
                  r1 ≠ r2 →
                  not-both-pair r1 r2 →
                  not-both-ctor r1 r2 →
                  ⌈ r1 ⌉:= v1 →
                  A == (r2 , v1) :: [] →
                  r1 ≡⌊ A ⌋ r2

  -- Generic result consistency failure - this goes through if results are not consistent
  data _≢_ : result → result → Set where
    RCFPair1    : ∀{r1 r2 r'1 r'2} →
                    r1 ≢ r'1 →
                    ⟨ r1 , r2 ⟩ ≢ ⟨ r'1 , r'2 ⟩
    RCFPair2    : ∀{r1 r2 r'1 r'2} →
                    r2 ≢ r'2 →
                    ⟨ r1 , r2 ⟩ ≢ ⟨ r'1 , r'2 ⟩
    RCFCtorMM   : ∀{c c' r r'} →
                    c ≠ c' →
                    (C[ c ] r) ≢ (C[ c' ] r')
    RCFCtor     : ∀{c r r'} →
                    r ≢ r' →
                    (C[ c ] r) ≢ (C[ c ] r')
    RCFNoCoerce : ∀{r r'} →
                    r ≠ r' →
                    not-both-pair r r' →
                    not-both-ctor r r' →
                    (∀{v} → ⌈ r  ⌉:= v → ⊥) →
                    (∀{v} → ⌈ r' ⌉:= v → ⊥) →
                    r ≢ r'

  -- Various judgments accept "fuel", which defines whether or not they can recurse indefinitely,
  -- and, if not, then the numerical limit. The limit is not on the recursion depth, but rather
  -- on the number of "beta reductions", interpreted a bit loosely to include case evaluations.
  -- - If ⌊ ⛽ ⌋ is ∞, then there is no beta reduction limit,
  --   but the judgment will not be satisfied unless evaluation eventually terminates.
  -- - If ⌊ ⛽ ⌋ is ⛽⟨ n ⟩, then the beta reduction limit is at most n,
  --   but if the limit is reached, then "success" judgments will not go through,
  --   but "failure" judgments will be satisfied automatically.
  data Fuel : Set where
    ∞ : Fuel
    ⛽⟨_⟩ : Nat → Fuel

  -- fuel depletion
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
    EUnit       : ∀{E ⛽} → E ⊢ ⟨⟩ ⌊ ⛽ ⌋⇒ ⟨⟩ ⊣ []
    EPair       : ∀{E ⛽ e1 e2 r1 r2 A1 A2} →
                    E ⊢ e1 ⌊ ⛽ ⌋⇒ r1 ⊣ A1 →
                    E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ A2 →
                    E ⊢ ⟨ e1 , e2 ⟩ ⌊ ⛽ ⌋⇒ ⟨ r1 , r2 ⟩ ⊣ A1 ++ A2
    ECtor       : ∀{E ⛽ c e r A} →
                    E ⊢ e ⌊ ⛽ ⌋⇒ r ⊣ A →
                    E ⊢ C[ c ] e ⌊ ⛽ ⌋⇒ (C[ c ] r) ⊣ A
    EFix        : ∀{E ⛽ f x e} → E ⊢ fix f ⦇·λ x => e ·⦈ ⌊ ⛽ ⌋⇒ [ E ]fix f ⦇·λ x => e ·⦈ ⊣ []
    EVar        : ∀{E ⛽ x r} → (x , r) ∈ E → E ⊢ X[ x ] ⌊ ⛽ ⌋⇒ r ⊣ []
    EHole       : ∀{E ⛽ u} → E ⊢ ??[ u ] ⌊ ⛽ ⌋⇒ [ E ]??[ u ] ⊣ []
    EAppFix     : ∀{E ⛽ ⛽↓ e1 e2 Ef f x ef r1 A1 r2 A2 r A} →
                    ⛽ ⛽⇓ ⛽↓ →
                    E ⊢ e1 ⌊ ⛽ ⌋⇒ r1 ⊣ A1 →
                    r1 == [ Ef ]fix f ⦇·λ x => ef ·⦈ →
                    E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ A2 →
                    (Ef ,, (f , r1) ,, (x , r2)) ⊢ ef ⌊ ⛽↓ ⌋⇒ r ⊣ A →
                    E ⊢ e1 ∘ e2 ⌊ ⛽ ⌋⇒ r ⊣ A1 ++ A2 ++ A
    EAppIndet   : ∀{E ⛽ e1 e2 r1 A1 r2 A2} →
                    E ⊢ e1 ⌊ ⛽ ⌋⇒ r1 ⊣ A1 →
                    (∀{Ef f x ef} → r1 ≠ [ Ef ]fix f ⦇·λ x => ef ·⦈) →
                    E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ A2 →
                    E ⊢ e1 ∘ e2 ⌊ ⛽ ⌋⇒ (r1 ∘ r2) ⊣ A1 ++ A2
    EPrj        : ∀{E ⛽ i e r1 r2 A} →
                    E ⊢ e ⌊ ⛽ ⌋⇒ ⟨ r1 , r2 ⟩ ⊣ A →
                    E ⊢ prj[ i ] e ⌊ ⛽ ⌋⇒ prj i r1 r2 ⊣ A
    EPrjIndet   : ∀{E ⛽ i e r A} →
                    E ⊢ e ⌊ ⛽ ⌋⇒ r ⊣ A →
                    (∀{r1 r2} → r ≠ ⟨ r1 , r2 ⟩) →
                    E ⊢ prj[ i ] e ⌊ ⛽ ⌋⇒ prj[ i ] r ⊣ A
    ECase       : ∀{E ⛽ ⛽↓ e rules c xc ec r A' rc A} →
                    ⛽ ⛽⇓ ⛽↓ →
                    (c , |C xc => ec) ∈ rules →
                    E ⊢ e ⌊ ⛽ ⌋⇒ (C[ c ] r) ⊣ A →
                    (E ,, (xc , r)) ⊢ ec ⌊ ⛽↓ ⌋⇒ rc ⊣ A' →
                    E ⊢ case e of⦃· rules ·⦄ ⌊ ⛽ ⌋⇒ rc ⊣ A ++ A'
    ECaseIndet  : ∀{E ⛽ e rules r A} →
                    E ⊢ e ⌊ ⛽ ⌋⇒ r ⊣ A →
                    (∀{c rc} → r ≠ (C[ c ] rc)) →
                    E ⊢ case e of⦃· rules ·⦄ ⌊ ⛽ ⌋⇒ [ E ]case r of⦃· rules ·⦄ ⊣ A
    EAssert     : ∀{E ⛽ e1 r1 A1 e2 r2 A2 A3} →
                    E ⊢ e1 ⌊ ⛽ ⌋⇒ r1 ⊣ A1 →
                    E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ A2 →
                    r1 ≡⌊ A3 ⌋ r2 →
                    E ⊢ PBE:assert e1 e2 ⌊ ⛽ ⌋⇒ ⟨⟩ ⊣ A1 ++ A2 ++ A3

  -- Generic evaluation failure - this goes through if evaluation would fail due to failure
  -- of some assertion that occurs during evaluation, or if the fuel runs out.
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
    EFAppEval    : ∀{E ⛽ ⛽↓ e1 e2 Ef f x ef r1 A1 r2 A2} →
                     ⛽ ⛽⇓ ⛽↓ →
                     E ⊢ e1 ⌊ ⛽ ⌋⇒ r1 ⊣ A1 →
                     r1 == [ Ef ]fix f ⦇·λ x => ef ·⦈ →
                     E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ A2 →
                     (Ef ,, (f , r1) ,, (x , r2)) ⊢ ef ⌊ ⛽↓ ⌋⇒∅ →
                     E ⊢ e1 ∘ e2 ⌊ ⛽ ⌋⇒∅
    EFPrj        : ∀{E ⛽ i e} →
                     E ⊢ e ⌊ ⛽ ⌋⇒∅ →
                     E ⊢ prj[ i ] e ⌊ ⛽ ⌋⇒∅
    EFCaseScrut  : ∀{E ⛽ e rules} →
                     E ⊢ e ⌊ ⛽ ⌋⇒∅ →
                     E ⊢ case e of⦃· rules ·⦄ ⌊ ⛽ ⌋⇒∅
    EFCaseRule   : ∀{E ⛽ ⛽↓ e rules c xc ec r A} →
                     ⛽ ⛽⇓ ⛽↓ →
                     (c , |C xc => ec) ∈ rules →
                     E ⊢ e ⌊ ⛽ ⌋⇒ (C[ c ] r) ⊣ A →
                     (E ,, (xc , r)) ⊢ ec ⌊ ⛽↓ ⌋⇒∅ →
                     E ⊢ case e of⦃· rules ·⦄ ⌊ ⛽ ⌋⇒∅
    EFAssert1    : ∀{E ⛽ e1 e2} →
                     E ⊢ e1 ⌊ ⛽ ⌋⇒∅ →
                     E ⊢ PBE:assert e1 e2 ⌊ ⛽ ⌋⇒∅
    EFAssert2    : ∀{E ⛽ e1 e2} →
                     E ⊢ e2 ⌊ ⛽ ⌋⇒∅ →
                     E ⊢ PBE:assert e1 e2 ⌊ ⛽ ⌋⇒∅
    EFAssert     : ∀{E ⛽ e1 r1 A1 e2 r2 A2} →
                     E ⊢ e1 ⌊ ⛽ ⌋⇒ r1 ⊣ A1 →
                     E ⊢ e2 ⌊ ⛽ ⌋⇒ r2 ⊣ A2 →
                     r1 ≢ r2 →
                     E ⊢ PBE:assert e1 e2 ⌊ ⛽ ⌋⇒∅
    EFLimit      : ∀{E e} → E ⊢ e ⌊ ⛽⟨ 0 ⟩ ⌋⇒∅

  -- resumption
  mutual
    data _⊢_⌊_⌋:⇨_:=_ : hole-fillings → env → Fuel → env → assertions → Set where
      RENil : ∀{⛽ F} → F ⊢ ∅ ⌊ ⛽ ⌋:⇨ ∅ := []
      REInd : ∀{⛽ F E E' x r r' A A'} →
                F ⊢ E ⌊ ⛽ ⌋:⇨ E' := A →
                F ⊢ r ⌊ ⛽ ⌋⇨ r' := A' →
                F ⊢ E ,, (x , r) ⌊ ⛽ ⌋:⇨ (E' ,, (x , r')) := A ++ A'

    data _⊢_⌊_⌋⇨_:=_ : hole-fillings → result → Fuel → result → assertions → Set where
      RHoleResume  : ∀{⛽ F E u r r' e A A'} →
                       (u , e) ∈ F →
                       E ⊢ e ⌊ ⛽ ⌋⇒ r ⊣ A →
                       F ⊢ r ⌊ ⛽ ⌋⇨ r' := A' →
                       F ⊢ [ E ]??[ u ] ⌊ ⛽ ⌋⇨ r' := A ++ A'
      RHoleIndet   : ∀{⛽ F E E' u A} →
                       u # F →
                       F ⊢ E ⌊ ⛽ ⌋:⇨ E' := A →
                       F ⊢ [ E ]??[ u ] ⌊ ⛽ ⌋⇨ [ E' ]??[ u ] := A
      RUnit        : ∀{⛽ F} → F ⊢ ⟨⟩ ⌊ ⛽ ⌋⇨ ⟨⟩ := []
      RPair        : ∀{⛽ F r1 r2 r1' r2' A1 A2} →
                       F ⊢ r1 ⌊ ⛽ ⌋⇨ r1' := A1 →
                       F ⊢ r2 ⌊ ⛽ ⌋⇨ r2' := A2 →
                       F ⊢ ⟨ r1 , r2 ⟩ ⌊ ⛽ ⌋⇨ ⟨ r1' , r2' ⟩ := A1 ++ A2
      RCtor        : ∀{⛽ F c r r' A} →
                       F ⊢ r ⌊ ⛽ ⌋⇨ r' := A →
                       F ⊢ C[ c ] r ⌊ ⛽ ⌋⇨ (C[ c ] r') := A
      RApp         : ∀{⛽ ⛽↓ F r1 r2 r r' Ef f x ef r1' r2' A1 A2 Af A'} →
                       ⛽ ⛽⇓ ⛽↓ →
                       F ⊢ r1 ⌊ ⛽ ⌋⇨ r1' := A1 →
                       r1' == [ Ef ]fix f ⦇·λ x => ef ·⦈ →
                       F ⊢ r2 ⌊ ⛽ ⌋⇨ r2' := A2 →
                       (Ef ,, (f , r1') ,, (x , r2')) ⊢ ef ⌊ ⛽↓ ⌋⇒ r ⊣ Af →
                       F ⊢ r ⌊ ⛽↓ ⌋⇨ r' := A' →
                       F ⊢ r1 ∘ r2 ⌊ ⛽ ⌋⇨ r' := A1 ++ A2 ++ Af ++ A'
      RAppIndet    : ∀{⛽ F r1 r2 r1' r2' A1 A2} →
                       F ⊢ r1 ⌊ ⛽ ⌋⇨ r1' := A1 →
                       (∀{Ef f x ef} → r1' ≠ [ Ef ]fix f ⦇·λ x => ef ·⦈) →
                       F ⊢ r2 ⌊ ⛽ ⌋⇨ r2' := A2 →
                       F ⊢ r1 ∘ r2 ⌊ ⛽ ⌋⇨ (r1' ∘ r2') := A1 ++ A2
      RFix         : ∀{⛽ F E E' f x e A} →
                       F ⊢ E ⌊ ⛽ ⌋:⇨ E' := A →
                       F ⊢ [ E ]fix f ⦇·λ x => e ·⦈ ⌊ ⛽ ⌋⇨ [ E' ]fix f ⦇·λ x => e ·⦈ := A
      RPrj         : ∀{⛽ F i r r1 r2 A} →
                       F ⊢ r ⌊ ⛽ ⌋⇨ ⟨ r1 , r2 ⟩ := A →
                       F ⊢ prj[ i ] r ⌊ ⛽ ⌋⇨ prj i r1 r2 := A
      RPrjIndet    : ∀{⛽ F i r r' A} →
                       F ⊢ r ⌊ ⛽ ⌋⇨ r' := A →
                       (∀{r1 r2} → r' ≠ ⟨ r1 , r2 ⟩) →
                       F ⊢ prj[ i ] r ⌊ ⛽ ⌋⇨ prj[ i ] r' := A
      RCase        : ∀{⛽ F E r rules c xc ec r' rc A A'} →
                       (c , |C xc => ec) ∈ rules →
                       F ⊢ r ⌊ ⛽ ⌋⇨ (C[ c ] r') := A →
                       F ⊢ [ E ]fix xc ⦇·λ xc => ec ·⦈ ∘ (C⁻¹[ c ] r) ⌊ ⛽ ⌋⇨ rc := A' →
                       F ⊢ [ E ]case r of⦃· rules ·⦄ ⌊ ⛽ ⌋⇨ rc := A ++ A'
      RCaseIndet   : ∀{⛽ F E E' r rules r' A A'} →
                       F ⊢ r ⌊ ⛽ ⌋⇨ r' := A →
                       (∀{c rc} → r' ≠ (C[ c ] rc)) →
                       F ⊢ E ⌊ ⛽ ⌋:⇨ E' := A' →
                       F ⊢ [ E ]case r of⦃· rules ·⦄ ⌊ ⛽ ⌋⇨ [ E' ]case r' of⦃· rules ·⦄ := A ++ A'
      RUnwrapCtor  : ∀{⛽ F r c rc A} →
                       F ⊢ r ⌊ ⛽ ⌋⇨ C[ c ] rc := A →
                       F ⊢ C⁻¹[ c ] r ⌊ ⛽ ⌋⇨ rc := A
      RUnwrapIndet : ∀{⛽ F c r r' A} →
                       F ⊢ r ⌊ ⛽ ⌋⇨ r' := A →
                       (∀{rc} → r' ≠ (C[ c ] rc)) →
                       F ⊢ C⁻¹[ c ] r ⌊ ⛽ ⌋⇨ C⁻¹[ c ] r' := A

  -- Generic resumption failure - this goes through if resumption would fail due to failure
  -- of some evaluation that occurs during resumption.
  mutual
    data _⊢_⌊_⌋:⇨∅ : hole-fillings → env → Fuel → Set where
      RFERes : ∀{⛽ F E x r} →
                 F ⊢ r ⌊ ⛽ ⌋⇨∅ →
                 F ⊢ (E ,, (x , r)) ⌊ ⛽ ⌋:⇨∅
      RFEEnv : ∀{⛽ F E x r} →
                 F ⊢ E ⌊ ⛽ ⌋:⇨∅ →
                 F ⊢ (E ,, (x , r)) ⌊ ⛽ ⌋:⇨∅

      {- TODO we must choose between this approach and the one prior
      RFE : ∀{⛽ F E x r} →
              (x , r) ∈ E →
              F ⊢ r ⌊ ⛽ ⌋⇨∅ →
              F ⊢ E ⌊ ⛽ ⌋:⇨∅
      -}

    data _⊢_⌊_⌋⇨∅ : hole-fillings → result → Fuel → Set where
      RFHoleEval   : ∀{⛽ F E u e} →
                       (u , e) ∈ F →
                       E ⊢ e ⌊ ⛽ ⌋⇒∅ →
                       F ⊢ [ E ]??[ u ] ⌊ ⛽ ⌋⇨∅
      RFHoleRes    : ∀{⛽ F E u e r A} →
                       (u , e) ∈ F →
                       E ⊢ e ⌊ ⛽ ⌋⇒ r ⊣ A →
                       F ⊢ r ⌊ ⛽ ⌋⇨∅ →
                       F ⊢ [ E ]??[ u ] ⌊ ⛽ ⌋⇨∅
      RFHoleIndet  : ∀{⛽ F E u} →
                       u # F →
                       F ⊢ E ⌊ ⛽ ⌋:⇨∅ →
                       F ⊢ [ E ]??[ u ] ⌊ ⛽ ⌋⇨∅
      RFPair1      : ∀{⛽ F r1 r2} →
                       F ⊢ r1 ⌊ ⛽ ⌋⇨∅ →
                       F ⊢ ⟨ r1 , r2 ⟩ ⌊ ⛽ ⌋⇨∅
      RFPair2      : ∀{⛽ F r1 r2} →
                       F ⊢ r2 ⌊ ⛽ ⌋⇨∅ →
                       F ⊢ ⟨ r1 , r2 ⟩ ⌊ ⛽ ⌋⇨∅
      RFCtor       : ∀{⛽ F c r} →
                       F ⊢ r ⌊ ⛽ ⌋⇨∅ →
                       F ⊢ C[ c ] r ⌊ ⛽ ⌋⇨∅
      RFAppFun     : ∀{⛽ F r1 r2} →
                       F ⊢ r1 ⌊ ⛽ ⌋⇨∅ →
                       F ⊢ r1 ∘ r2 ⌊ ⛽ ⌋⇨∅
      RFAppArg     : ∀{⛽ F r1 r2} →
                       F ⊢ r2 ⌊ ⛽ ⌋⇨∅ →
                       F ⊢ r1 ∘ r2 ⌊ ⛽ ⌋⇨∅
      RFAppEval    : ∀{⛽ ⛽↓ F r1 r2 Ef f x ef r1' r2' A1 A2} →
                       ⛽ ⛽⇓ ⛽↓ →
                       F ⊢ r1 ⌊ ⛽ ⌋⇨ r1' := A1 →
                       r1' == [ Ef ]fix f ⦇·λ x => ef ·⦈ →
                       F ⊢ r2 ⌊ ⛽ ⌋⇨ r2' := A2 →
                       (Ef ,, (f , r1') ,, (x , r2')) ⊢ ef ⌊ ⛽↓ ⌋⇒∅ →
                       F ⊢ r1 ∘ r2 ⌊ ⛽ ⌋⇨∅
      RFAppRes     : ∀{⛽ ⛽↓ F r1 r2 Ef f x ef r1' r2' r A1 A2 Af} →
                       ⛽ ⛽⇓ ⛽↓ →
                       F ⊢ r1 ⌊ ⛽ ⌋⇨ r1' := A1 →
                       r1' == [ Ef ]fix f ⦇·λ x => ef ·⦈ →
                       F ⊢ r2 ⌊ ⛽ ⌋⇨ r2' := A2 →
                       (Ef ,, (f , r1') ,, (x , r2')) ⊢ ef ⌊ ⛽↓ ⌋⇒ r ⊣ Af →
                       F ⊢ r ⌊ ⛽↓ ⌋⇨∅ →
                       F ⊢ r1 ∘ r2 ⌊ ⛽ ⌋⇨∅
      RFFix        : ∀{⛽ F E f x e} →
                       F ⊢ E ⌊ ⛽ ⌋:⇨∅ →
                       F ⊢ [ E ]fix f ⦇·λ x => e ·⦈ ⌊ ⛽ ⌋⇨∅
      RFPrj        : ∀{⛽ F i r} →
                       F ⊢ r ⌊ ⛽ ⌋⇨∅ →
                       F ⊢ prj[ i ] r ⌊ ⛽ ⌋⇨∅
      RFCaseScrut  : ∀{⛽ F E r rules} →
                       F ⊢ r ⌊ ⛽ ⌋⇨∅ →
                       F ⊢ [ E ]case r of⦃· rules ·⦄ ⌊ ⛽ ⌋⇨∅
      RFCase       : ∀{⛽ F E r rules c xc ec r' A} →
                       (c , |C xc => ec) ∈ rules →
                       F ⊢ r ⌊ ⛽ ⌋⇨ (C[ c ] r') := A →
                       F ⊢ [ E ]fix xc ⦇·λ xc => ec ·⦈ ∘ (C⁻¹[ c ] r) ⌊ ⛽ ⌋⇨∅ →
                       F ⊢ [ E ]case r of⦃· rules ·⦄ ⌊ ⛽ ⌋⇨∅
      RFCaseIndet  : ∀{⛽ F E r rules r' A} →
                       F ⊢ r ⌊ ⛽ ⌋⇨ r' := A →
                       (∀{c rc} → r' ≠ (C[ c ] rc)) →
                       F ⊢ E ⌊ ⛽ ⌋:⇨∅ →
                       F ⊢ [ E ]case r of⦃· rules ·⦄ ⌊ ⛽ ⌋⇨∅
      RFUnwrapCtor : ∀{⛽ F c r} →
                       F ⊢ r ⌊ ⛽ ⌋⇨∅ →
                       F ⊢ C⁻¹[ c ] r ⌊ ⛽ ⌋⇨∅
      RFLimit      : ∀{F r} → F ⊢ r ⌊ ⛽⟨ 0 ⟩ ⌋⇨∅

  data Filter_:=_ : excons → excons → Set where
    FilterNil : Filter [] := []
    FilterYes : ∀{X X' E ex} →
                  Filter X := X' →
                  ex ≠ ¿¿ →
                  Filter (E , ex) :: X := ((E , ex) :: X')
    FilterNo  : ∀{X X' E} →
                  Filter X := X' →
                  Filter (E , ¿¿) :: X := X'

  -- Assertion Satisfaction and Simplification
  data _⌊_⌋⊨ᴬ_ : hole-fillings → Fuel → assertions → Set where
    SANil : ∀{⛽ F} → F ⌊ ⛽ ⌋⊨ᴬ []
    SAInd : ∀{⛽ F r v r' A A'} →
              F ⌊ ⛽ ⌋⊨ᴬ A →
              F ⊢ r ⌊ ⛽ ⌋⇨ r' := A' →
              F ⌊ ⛽ ⌋⊨ᴬ A' →
              ⌈ r' ⌉:= v →
              F ⌊ ⛽ ⌋⊨ᴬ ((r , v) :: A)

  -- Example Satisfaction (of Results)
  data _⊢_⌊_⌋⊨ᴿ_ : hole-fillings → result → Fuel → ex → Set where
    XSTop   : ∀{⛽ F r} → F ⊢ r ⌊ ⛽ ⌋⊨ᴿ ¿¿
    XSUnit  : ∀{⛽ F} → F ⊢ ⟨⟩ ⌊ ⛽ ⌋⊨ᴿ ⟨⟩
    XSPair  : ∀{⛽ F r1 r2 ex1 ex2} →
                F ⊢ r1 ⌊ ⛽ ⌋⊨ᴿ ex1 →
                F ⊢ r2 ⌊ ⛽ ⌋⊨ᴿ ex2 →
                F ⊢ ⟨ r1 , r2 ⟩ ⌊ ⛽ ⌋⊨ᴿ ⟨ ex1 , ex2 ⟩
    XSCtor  : ∀{⛽ F r c ex} →
                F ⊢ r ⌊ ⛽ ⌋⊨ᴿ ex →
                F ⊢ C[ c ] r ⌊ ⛽ ⌋⊨ᴿ (C[ c ] ex)
    XSInOut : ∀{⛽ F r1 r2 v2 ex r A} →
                ⌈ r2 ⌉:= v2 →
                F ⊢ r1 ∘ r2 ⌊ ⛽ ⌋⇨ r := A →
                F ⊢ r ⌊ ⛽ ⌋⊨ᴿ ex →
                F ⌊ ⛽ ⌋⊨ᴬ A →
                F ⊢ r1 ⌊ ⛽ ⌋⊨ᴿ (v2 ↦ ex)

  -- Example Satisfaction (of Expressions)
  data _⊢_⌊_⌋⊨ᴱ_ : hole-fillings → exp → Fuel → excons → Set where
    SatNil : ∀{⛽ F e} → F ⊢ e ⌊ ⛽ ⌋⊨ᴱ []
    SatTop : ∀{⛽ F e E X} →
               F ⊢ e ⌊ ⛽ ⌋⊨ᴱ X →
               F ⊢ e ⌊ ⛽ ⌋⊨ᴱ ((E , ¿¿) :: X)
    SatInd : ∀{⛽ F e E ex X r r' A A'} →
               ex ≠ ¿¿ →
               F ⊢ e ⌊ ⛽ ⌋⊨ᴱ X →
               E ⊢ e ⌊ ⛽ ⌋⇒ r ⊣ A →
               F ⊢ r ⌊ ⛽ ⌋⇨ r' := A' →
               F ⊢ r' ⌊ ⛽ ⌋⊨ᴿ ex →
               F ⌊ ⛽ ⌋⊨ᴬ A ++ A' →
               F ⊢ e ⌊ ⛽ ⌋⊨ᴱ ((E , ex) :: X)

  data _⌊_⌋⊨ᵁ_ : hole-fillings → Fuel → excons ctx → Set where
    CSNil : ∀{⛽ F} → F ⌊ ⛽ ⌋⊨ᵁ ∅
    CSInd : ∀{⛽ F U u X} →
              F ⌊ ⛽ ⌋⊨ᵁ U →
              F ⊢ ??[ u ] ⌊ ⛽ ⌋⊨ᴱ X →
              F ⌊ ⛽ ⌋⊨ᵁ (U ,, (u , X))

  -- Constraint Satisfaction
  _⌊_⌋⊨ᴷ_ : hole-fillings → Fuel → constraints → Set
  F ⌊ ⛽ ⌋⊨ᴷ (F0 , U) =
    (∀{u e} → (u , e) ∈ F0 → (u , e) ∈ F) ∧
    F ⌊ ⛽ ⌋⊨ᵁ U

  -- constraints merge
  _⊕_:=_ : constraints → constraints → constraints → Set
  (F1 , U1) ⊕ (F2 , U2) := (F' , U') = F1 ≈ F2 ∧ F1 ∪ F2 == F' ∧ U1 ⊎ U2 == U'

  mutual
    -- example unevaluation
    data _,_,_⊢_⇐⌊_⌋_:=_ : hctx → denv → hole-fillings → result → Fuel → ex → constraints → Set where
      UTop        : ∀{⛽ Δ Σ' F r} → Δ , Σ' , F ⊢ r ⇐⌊ ⛽ ⌋ ¿¿ := (∅ , ∅)
      UHole       : ∀{⛽ Δ Σ' F E u ex} →
                      ex ≠ ¿¿ →
                      Δ , Σ' , F ⊢ [ E ]??[ u ] ⇐⌊ ⛽ ⌋ ex := (∅ , ■ (u , (E , ex) :: []))
      UUnit       : ∀{⛽ Δ Σ' F} → Δ , Σ' , F ⊢ ⟨⟩ ⇐⌊ ⛽ ⌋ ⟨⟩ := (∅ , ∅)
      UCtor       : ∀{⛽ Δ Σ' F c r ex K} →
                      Δ , Σ' , F ⊢ r ⇐⌊ ⛽ ⌋ ex := K →
                      Δ , Σ' , F ⊢ C[ c ] r ⇐⌊ ⛽ ⌋ C[ c ] ex := K
      UPair       : ∀{⛽ Δ Σ' F r1 r2 ex1 ex2 K1 K2 K'} →
                      Δ , Σ' , F ⊢ r1 ⇐⌊ ⛽ ⌋ ex1 := K1 →
                      Δ , Σ' , F ⊢ r2 ⇐⌊ ⛽ ⌋ ex2 := K2 →
                      K1 ⊕ K2 := K' →
                      Δ , Σ' , F ⊢ ⟨ r1 , r2 ⟩ ⇐⌊ ⛽ ⌋ ⟨ ex1 , ex2 ⟩ := K'
      UFix        : ∀{⛽ ⛽↓ Δ Σ' F E f x e rf v r ex K} →
                      ⛽ ⛽⇓ ⛽↓ →
                      rf == [ E ]fix f ⦇·λ x => e ·⦈ →
                      ⌈ r ⌉:= v →
                      Δ , Σ' , F ⊢ e ⌊ ⛽ ⌋⇌ ((E ,, (f , rf) ,, (x , r)) , ex) :: [] := K →
                      Δ , Σ' , F ⊢ rf ⇐⌊ ⛽ ⌋ v ↦ ex := K
      UApp        : ∀{⛽ Δ Σ' F r1 r2 ex v2 K} →
                      ex ≠ ¿¿ →
                      ⌈ r2 ⌉:= v2 →
                      Δ , Σ' , F ⊢ r1 ⇐⌊ ⛽ ⌋ v2 ↦ ex := K →
                      Δ , Σ' , F ⊢ r1 ∘ r2 ⇐⌊ ⛽ ⌋ ex := K
      UPrj1       : ∀{⛽ Δ Σ' F r ex K} →
                      ex ≠ ¿¿ →
                      Δ , Σ' , F ⊢ r ⇐⌊ ⛽ ⌋ ⟨ ex , ¿¿ ⟩ := K →
                      Δ , Σ' , F ⊢ prj[ P1 ] r ⇐⌊ ⛽ ⌋ ex := K
      UPrj2       : ∀{⛽ Δ Σ' F r ex K} →
                      ex ≠ ¿¿ →
                      Δ , Σ' , F ⊢ r ⇐⌊ ⛽ ⌋ ⟨ ¿¿ , ex ⟩ := K →
                      Δ , Σ' , F ⊢ prj[ P2 ] r ⇐⌊ ⛽ ⌋ ex := K
      UCase       : ∀{⛽ ⛽↓ Δ Σ' F E r rules ex c xc ec K1 K2 K'} →
                      ex ≠ ¿¿ →
                      ⛽ ⛽⇓ ⛽↓ →
                      (c , |C xc => ec) ∈ rules →
                      Δ , Σ' , F ⊢ r ⇐⌊ ⛽ ⌋ C[ c ] ¿¿ := K1 →
                      Δ , Σ' , F ⊢ ec ⌊ ⛽↓ ⌋⇌ ((E ,, (xc , C⁻¹[ c ] r)) , ex) :: [] := K2 →
                      K1 ⊕ K2 := K' →
                      Δ , Σ' , F ⊢ [ E ]case r of⦃· rules ·⦄ ⇐⌊ ⛽ ⌋ ex := K'
      UCaseGuess  : ∀{⛽ ⛽↓ Δ Σ' F F' E r rules ex c xc ec r' A K K' Kₘ₁ Kₘ₂} →
                      ex ≠ ¿¿ →
                      ⛽ ⛽⇓ ⛽↓ →
                      (c , |C xc => ec) ∈ rules →
                      Δ , Σ' ⊢ᴴ F' →
                      F ## F' →
                      F ∪ F' ⊢ r ⌊ ⛽ ⌋⇨ C[ c ] r' := A →
                      Δ , Σ' ⊢Simplify A ⌊ ⛽ ⌋:= K →
                      Δ , Σ' , F ∪ F' ⊢ ec ⌊ ⛽↓ ⌋⇌ ((E ,, (xc , r')) , ex) :: [] := K' →
                      K ⊕ K' := Kₘ₁ →
                      (F' , ∅) ⊕ Kₘ₁ := Kₘ₂ →
                      Δ , Σ' , F ⊢ [ E ]case r of⦃· rules ·⦄ ⇐⌊ ⛽ ⌋ ex := Kₘ₂
      UUnwrapCtor : ∀{⛽ Δ Σ' F c r ex K} →
                      ex ≠ ¿¿ →
                      Δ , Σ' , F ⊢ r ⇐⌊ ⛽ ⌋ C[ c ] ex := K →
                      Δ , Σ' , F ⊢ C⁻¹[ c ] r ⇐⌊ ⛽ ⌋ ex := K

    -- Assertion Simplification
    data _,_⊢Simplify_⌊_⌋:=_ : hctx → denv → assertions → Fuel → constraints → Set where
      SNil : ∀{⛽ Δ Σ'} → Δ , Σ' ⊢Simplify [] ⌊ ⛽ ⌋:= (∅ , ∅)
      SInd : ∀{⛽ Δ Σ' r v A K K' K''} →
               Δ , Σ' ⊢Simplify A ⌊ ⛽ ⌋:= K →
               r final →
               Δ , Σ' , ∅ ⊢ r ⇐⌊ ⛽ ⌋ ⌊ v ⌋ := K' →
               K ⊕ K' := K'' →
               Δ , Σ' ⊢Simplify (r , v) :: A ⌊ ⛽ ⌋:= K''

    -- Live Bidirectional Example Checking
    data _,_,_⊢_⌊_⌋⇌_:=_ : hctx → denv → hole-fillings → exp → Fuel → excons → constraints → Set where
      ChkNil : ∀{⛽ Δ Σ' F e} → Δ , Σ' , F ⊢ e ⌊ ⛽ ⌋⇌ [] := (∅ , ∅)
      ChkInd : ∀{⛽ Δ Σ' F e E ex X r r' A A' K K' K'' Kₘ₁ Kₘ₂} →
                 Δ , Σ' , F ⊢ e ⌊ ⛽ ⌋⇌ X := K →
                 E ⊢ e ⌊ ⛽ ⌋⇒ r ⊣ A →
                 F ⊢ r ⌊ ⛽ ⌋⇨ r' := A' →
                 Δ , Σ' , F ⊢ r' ⇐⌊ ⛽ ⌋ ex := K' →
                 Δ , Σ' ⊢Simplify A ++ A' ⌊ ⛽ ⌋:= K'' →
                 K' ⊕ K'' := Kₘ₁ →
                 K ⊕ Kₘ₁ := Kₘ₂ →
                 Δ , Σ' , F ⊢ e ⌊ ⛽ ⌋⇌ ((E , ex) :: X) := Kₘ₂

  -- TODO theorems for all the things, including resumption, synthesis, solve, satisfaction, consistency, Group, and Filter

  -- Type-Directed Guessing
  data _⊢⦇_⊢●:_⦈:=ᴳ_ : denv → tctx → typ → exp → Set where
    GUnit : ∀{Σ' Γ} → Σ' ⊢⦇ Γ ⊢●: ⟨⟩ ⦈:=ᴳ ⟨⟩
    GPair : ∀{Σ' Γ τ1 τ2 e1 e2} →
              Σ' ⊢⦇ Γ ⊢●: τ1 ⦈:=ᴳ e1 →
              Σ' ⊢⦇ Γ ⊢●: τ2 ⦈:=ᴳ e2 →
              Σ' ⊢⦇ Γ ⊢●: ⟨ τ1 × τ2 ⟩ ⦈:=ᴳ ⟨ e1 , e2 ⟩
    GCtor : ∀{Σ' Γ d cctx c τ e} →
              (d , cctx) ∈ π1 Σ' →
              (c , τ) ∈ cctx →
              Σ' ⊢⦇ Γ ⊢●: τ ⦈:=ᴳ e →
              Σ' ⊢⦇ Γ ⊢●: D[ d ] ⦈:=ᴳ (C[ c ] e)
    GFix  : ∀{Σ' Γ τ1 τ2 f x e} →
              Σ' ⊢⦇ Γ ,, (f , τ1 ==> τ2) ,, (x , τ1) ⊢●: τ2 ⦈:=ᴳ e →
              Σ' ⊢⦇ Γ ⊢●: τ1 ==> τ2 ⦈:=ᴳ fix f ⦇·λ x => e ·⦈
    GCase : ∀{Σ' Γ τ e rules d cctx} →
              (d , cctx) ∈ π1 Σ' →
              (∀{c} → dom cctx c → dom rules c) →
              (∀{c} → dom rules c → dom cctx c) →
              Σ' ⊢⦇ Γ ⊢●: D[ d ] ⦈:=ᴳ e →
              (∀{c x-c e-c τ-c} →
                 (c , |C x-c => e-c) ∈ rules →
                 (c , τ-c) ∈ cctx →
                 Σ' ⊢⦇ Γ ,, (x-c , τ-c) ⊢●: τ ⦈:=ᴳ e-c) →
              Σ' ⊢⦇ Γ ⊢●: τ ⦈:=ᴳ case e of⦃· rules ·⦄
    GVar  : ∀{Σ' Γ τ x} →
              (x , τ) ∈ Γ →
              Σ' ⊢⦇ Γ ⊢●: τ ⦈:=ᴳ X[ x ]
    GApp  : ∀{Σ' Γ τ e1 e2 τ'} →
              Σ' ⊢⦇ Γ ⊢●: τ' ==> τ ⦈:=ᴳ e1 →
              Σ' ⊢⦇ Γ ⊢●: τ' ⦈:=ᴳ e2 →
              Σ' ⊢⦇ Γ ⊢●: τ ⦈:=ᴳ (e1 ∘ e2)
    GPrj  : ∀{Σ' Γ τ1 τ2 i e} →
              Σ' ⊢⦇ Γ ⊢●: ⟨ τ1 × τ2 ⟩ ⦈:=ᴳ e →
              Σ' ⊢⦇ Γ ⊢●: prj i τ1 τ2 ⦈:=ᴳ (prj[ i ] e)

  -- TODO theorem that if u # Δ , then u is new in a type-checked exp or result

  -- TODO theorem that any hole in the exp produced by refinement is in the goals

  -- Type-and-Example-Directed Refinement
  data _⊢⦇_⊢●:_⊨_⦈:=ᴿ_⊣_ : denv → tctx → typ → excons → exp → goals → Set where
    RefUnit : ∀{Σ' Γ X Xf} →
                Filter X := Xf →
                (∀{i E ex} → Xf ⟦ i ⟧ == Some (E , ex) → ex == ⟨⟩) →
                Σ' ⊢⦇ Γ ⊢●: ⟨⟩ ⊨ X ⦈:=ᴿ ⟨⟩ ⊣ []
    RefPair : ∀{Σ' Γ τ1 τ2 X u1 u2 G1 G2} {E-ex1-ex2s : List (env ∧ ex ∧ ex)} →
                Filter X := map (λ {(E , ex1 , ex2) → E , ⟨ ex1 , ex2 ⟩}) E-ex1-ex2s →
                G1 == Γ ⊢??[ u1 ]: τ1 ⊨ map (λ {(E , ex1 , ex2) → E , ex1}) E-ex1-ex2s →
                G2 == Γ ⊢??[ u2 ]: τ2 ⊨ map (λ {(E , ex1 , ex2) → E , ex2}) E-ex1-ex2s →
                Σ' ⊢⦇ Γ ⊢●: ⟨ τ1 × τ2 ⟩ ⊨ X ⦈:=ᴿ ⟨ ??[ u1 ] , ??[ u2 ] ⟩ ⊣ (G1 :: (G2 :: []))
    RefCtor : ∀{Σ' Γ X X' d cctx c τ u G} →
                (d , cctx) ∈ π1 Σ' →
                (c , τ) ∈ cctx →
                Filter X := map (λ {(E , ex) → E , C[ c ] ex}) X' →
                G == Γ ⊢??[ u ]: τ ⊨ X' →
                Σ' ⊢⦇ Γ ⊢●: D[ d ] ⊨ X ⦈:=ᴿ C[ c ] ??[ u ] ⊣ (G :: [])
    RefFix  : ∀{Σ' Γ X τ1 τ2 f x u X' G} {E-in-inᶜ-outs : List (env ∧ val ∧ result ∧ ex)} →
                (∀{i E-i v-i r-i ex-i} →
                   E-in-inᶜ-outs ⟦ i ⟧ == Some (E-i , v-i , r-i , ex-i) →
                   ⌈ r-i ⌉:= v-i) →
                Filter X := map (λ {(E , in' , _ , out) → E , in' ↦ out}) E-in-inᶜ-outs →
                X' == map (λ {(E , _ , in' , out) → (E ,, (f , [ E ]fix f ⦇·λ x => ??[ u ] ·⦈) ,, (x , in')) , out}) E-in-inᶜ-outs →
                G == (Γ ,, (f , τ1 ==> τ2) ,, (x , τ1)) ⊢??[ u ]: τ2 ⊨ X' →
                Σ' ⊢⦇ Γ ⊢●: τ1 ==> τ2 ⊨ X ⦈:=ᴿ fix f ⦇·λ x => ??[ u ] ·⦈ ⊣ (G :: [])

  -- Type-and-Example-Directed Branching
  data _⊢⦇_⊢●:_⊨_⦈⌊_⌋:=ᴮ_⊣_ : denv → tctx → typ → excons → Fuel → exp → goals → Set where
    BCase : ∀{⛽ Σ' Γ X Xf τ e rules d cctx x τ+u+X⁺-ctx Gs} →
              Filter X := Xf →
              -- choose one fresh variable name that will be used for all cases
              x # Γ →
              -- τ+u+X⁺-ctx is just cctx extended with hole names and excons
              cctx == ctxmap π1 τ+u+X⁺-ctx →
              -- the rules can be defined from x and the hole names in τ+u+X⁺-ctx
              rules == ctxmap (λ {(τ-c , u-c , X⁺-c) → |C x => ??[ u-c ]}) τ+u+X⁺-ctx →
              -- the following premises appear in the paper
              (d , cctx) ∈ π1 Σ' →
              Σ' ⊢⦇ Γ ⊢●: D[ d ] ⦈:=ᴳ e →
              Gs == map
                 (λ {(τ-c , u-c , X⁺-c) →
                    -- this corresponds to the goal definition in the paper
                    (Γ ,, (x , τ-c)) ⊢??[ u-c ]: τ ⊨
                       -- this corresponds to the definition of each X_i in the paper
                       map (λ {(E , ex , r) → (E ,, (x , r)) , ex}) X⁺-c})
                 (ctx⇒values τ+u+X⁺-ctx) →
              -- the following premise checks that every X⁺-c obeys the rules in the paper premise
              (∀{c τ-c u-c X⁺-c} →
                 (c , τ-c , u-c , X⁺-c) ∈ τ+u+X⁺-ctx →
                 -- for each excon (extended with a result r-j) of X⁺-c, ...
                 (∀{j E-j ex-j r-j} →
                    X⁺-c ⟦ j ⟧ == Some (E-j , ex-j , r-j) →
                      -- the excon is an element of Filter X, and ...
                      Σ[ k ∈ Nat ] (Xf ⟦ k ⟧ == Some (E-j , ex-j)) ∧
                      -- the scrutinee e will evaluate to constructor c applied to the specified argument r-j
                      E-j ⊢ e ⌊ ⛽ ⌋⇒ C[ c ] r-j ⊣ [])) →
              -- the last premise in the paper - every excon in Filter X is an element of some X⁺-c for some c
              (∀{k E-k ex-k} →
                 Xf ⟦ k ⟧ == Some (E-k , ex-k) →
                 Σ[ c ∈ Nat ] Σ[ τ-c ∈ typ ] Σ[ u-c ∈ Nat ] Σ[ X⁺-c ∈ List (env ∧ ex ∧ result)] Σ[ j ∈ Nat ] Σ[ r-j ∈ result ] (
                    (c , τ-c , u-c , X⁺-c) ∈ τ+u+X⁺-ctx ∧
                    X⁺-c ⟦ j ⟧ == Some (E-k , ex-k , r-j))) →
              Σ' ⊢⦇ Γ ⊢●: τ ⊨ X ⦈⌊ ⛽ ⌋:=ᴮ case e of⦃· rules ·⦄ ⊣ Gs

  -- Hole Filling
  data _,_,_⊢⦇_⊢??[_]:_⊨_⦈⌊_⌋:=_,_ : hctx → denv → hole-fillings → tctx → Nat → typ → excons → Fuel → constraints → hctx → Set where
    HFRefBranch : ∀{⛽ Δ Σ' F Γ u τ X e Gs K Δ'} →
                    -- this premise ensures that all holes are fresh
                    (∀{i j g-i g-j} →
                       Gs ⟦ i ⟧ == Some g-i →
                       Gs ⟦ j ⟧ == Some g-j →
                         goal.g-id g-i # Δ ∧
                         goal.g-id g-i ≠ u ∧
                         (i ≠ j → goal.g-id g-i ≠ goal.g-id g-j)) →
                    (Σ' ⊢⦇ Γ ⊢●: τ ⊨ X ⦈:=ᴿ e ⊣ Gs ∨
                     Σ' ⊢⦇ Γ ⊢●: τ ⊨ X ⦈⌊ ⛽ ⌋:=ᴮ e ⊣ Gs) →
                    K == (■ (u , e) , list⇒ctx (map (λ {(_ ⊢??[ u' ]: _ ⊨ X') → u' , X'}) Gs)) →
                    Δ' == list⇒ctx (map (λ {(Γ' ⊢??[ u' ]: τ' ⊨ _) → u' , Γ' , τ'}) Gs) →
                    Δ , Σ' , F ⊢⦇ Γ ⊢??[ u ]: τ ⊨ X ⦈⌊ ⛽ ⌋:= K , Δ'
    HFGuessChk  : ∀{⛽ Δ Σ' F Γ u τ X e K K'} →
                    Σ' ⊢⦇ Γ ⊢●: τ ⦈:=ᴳ e →
                    Δ , Σ' , (F ,, (u , e)) ⊢ e ⌊ ⛽ ⌋⇌ X := K →
                    (■ (u , e) , ∅) ⊕ K := K' →
                    Δ , Σ' , F ⊢⦇ Γ ⊢??[ u ]: τ ⊨ X ⦈⌊ ⛽ ⌋:= K' , ∅
    HFDefer     : ∀{⛽ Δ Σ' F Γ u τ X} →
                    X ≠ [] →
                    Filter X := [] →
                    Δ , Σ' , F ⊢⦇ Γ ⊢??[ u ]: τ ⊨ X ⦈⌊ ⛽ ⌋:= (■ (u , ??[ u ]) , ∅) , ∅

  {- TODO - later, we need to fix this stuff up too
  data _,_IterSolve_,_⌊_⌋:=_,_ : hctx → denv → hole-fillings → excons ctx → Fuel → hole-fillings → hctx → Set where
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
                 Σ[ i ∈ Nat ] Σ[ F-i ∈ hole-fillings ] Σ[ U-i ∈ excons ctx ] Σ[ Δ-i ∈ hctx ] (
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
              Σ[ u-n ∈ Nat ] Σ[ U-n ∈ excons ctx ] (u+F+U+Δs ⟦ ∥ U ∥ ⟧ == Some (u-n , F-n , U-n , Δ-n)) →
              Δ-n , Σ' IterSolve F-n , U' ⌊ ⛽ ⌋:= F' , Δ' →
              Δ , Σ' IterSolve F-0 , U ⌊ ⛽ ⌋:= F' , Δ'

  data _,_Solve_⌊_⌋:=_ : hctx → denv → constraints → Fuel → hole-fillings → Set where
    Solve : ∀{⛽ Δ Σ' F0 U F Δ'} →
              Δ , Σ' IterSolve F0 , U ⌊ ⛽ ⌋:= F , Δ' →
              Δ , Σ' Solve (F0 , U) ⌊ ⛽ ⌋:= F
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
