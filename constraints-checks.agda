open import Nat
open import Prelude
open import List

open import contexts
open import core

open import preservation
open import decidability

module constraints-checks where
  {-
  TODO : We really do need to prove unicity of constraint collection and backpropagation,
         but they depend on evaluation unicity, which isn't proven yet and may be difficult
         to prove. So for now we comment out this proof, and we can come back to it later
         when we have more time.
  constraints-unicity : ∀{r1 r2 k k'} →
                          Constraints⦃ r1 , r2 ⦄:= k →
                          Constraints⦃ r1 , r2 ⦄:= k' →
                          k == k'
  constraints-unicity XCEx XCEx = refl
  constraints-unicity XCExSymm XCExSymm = refl
  constraints-unicity XCExRefl XCExRefl = refl
  constraints-unicity XCExRefl (XCTpl ne _ _ _) = abort (ne refl)
  constraints-unicity XCExRefl (XCCTor ne _) = abort (ne refl)
  constraints-unicity XCExRefl (XCAp ne _ _) = abort (ne refl)
  constraints-unicity XCExRefl (XCGet ne _) = abort (ne refl)
  constraints-unicity XCExRefl (XCMatch ne _) = abort (ne refl)
  constraints-unicity (XCTpl ne _ _ _) XCExRefl = abort (ne refl)
  constraints-unicity (XCTpl {rs1} {rs2} {ks1} _ ∥rs1∥==∥rs2∥ ∥rs1∥==∥ks1∥ h1) (XCTpl {ks = ks2} _ _ ∥rs1∥==∥ks2∥ h2)
    with ==-per-elem {l1 = ks1} {ks2} per-elem
         where
         per-elem : (i : Nat) → ks1 ⟦ i ⟧ == ks2 ⟦ i ⟧
         per-elem i
           with list-index-dec rs1 i
         ... | Inl rs1[i]==None
           rewrite ∥l1∥==∥l2∥→¬l1[i]→¬l2[i] ∥rs1∥==∥ks2∥ rs1[i]==None
             = ∥l1∥==∥l2∥→¬l1[i]→¬l2[i] ∥rs1∥==∥ks1∥ rs1[i]==None
         ... | Inr (_ , rs1[i]==r1-i)
           with ∥l1∥==∥l2∥→l1[i]→l2[i] ∥rs1∥==∥rs2∥ rs1[i]==r1-i
              | ∥l1∥==∥l2∥→l1[i]→l2[i] ∥rs1∥==∥ks1∥ rs1[i]==r1-i
              | ∥l1∥==∥l2∥→l1[i]→l2[i] ∥rs1∥==∥ks2∥ rs1[i]==r1-i
         ...  | _ , rs2[i]==r2-i | _ , ks1[i]==k1-i | _ , ks2[i]==k2-i
           with constraints-unicity (h1 rs1[i]==r1-i rs2[i]==r2-i ks1[i]==k1-i) (h2 rs1[i]==r1-i rs2[i]==r2-i ks2[i]==k2-i)
         ... | refl rewrite ks2[i]==k2-i = ks1[i]==k1-i
  ... | refl = refl
  constraints-unicity (XCCTor ne _) XCExRefl = abort (ne refl)
  constraints-unicity (XCCTor _ :=k) (XCCTor _ :=k') = constraints-unicity :=k :=k'
  constraints-unicity (XCAp ne _ _) XCExRefl = abort (ne refl)
  constraints-unicity (XCAp _ :=kf :=karg) (XCAp _ :=kf' :=karg')
    rewrite constraints-unicity :=kf' :=kf | constraints-unicity :=karg :=karg' = refl
  constraints-unicity (XCGet ne _) XCExRefl = abort (ne refl)
  constraints-unicity (XCGet _ :=k) (XCGet _ :=k') = constraints-unicity :=k :=k'
  constraints-unicity (XCMatch ne _) XCExRefl = abort (ne refl)
  constraints-unicity (XCMatch _ :=k) (XCMatch _ :=k') = constraints-unicity :=k :=k'
  -}

  {- TODO - we should probably have some theorems relating to this,
     but now that constraints checking takes fuel,
     it's no longer decidable in a simple fashion
  mutual
    constraints-dec : (r1 r2 : result) →
                        Σ[ k ∈ constraints ] Constraints⦃ r1 , r2 ⦄:= k
                        ∨ Constraints⦃ r1 , r2 ⦄:=∅
    constraints-dec r1 r2
      with result-==-dec r1 r2
    ... | Inl refl = Inl (_ , XCExRefl)
    constraints-dec ([ E ]λ x => e) _ | Inr r1≠r2
      = Inr (λ where (_ , XCExRefl) → r1≠r2 refl)
    constraints-dec [ E ]fix f ⦇·λ x => e ·⦈ _ | Inr r1≠r2
      = Inr (λ where (_ , XCExRefl) → r1≠r2 refl)
    constraints-dec ⟨ rs1 ⟩ ⟨ rs2 ⟩ | Inr r1≠r2
      with natEQ ∥ rs1 ∥ ∥ rs2 ∥
    ... | Inr ne = Inr λ
            { (_ , XCExRefl)                → ne refl ;
              (_ , XCTpl _ ∥rs1∥==∥rs2∥ _ _) → ne ∥rs1∥==∥rs2∥ }
    ... | Inl ∥rs1∥==∥rs2∥
      with list<constraints>-dec ∥rs1∥==∥rs2∥
    ... | Inl (_ , ∥rs1∥==∥ks∥ , C<children>)
            = Inl (_ , XCTpl r1≠r2 ∥rs1∥==∥rs2∥ ∥rs1∥==∥ks∥ C<children>)
    ... | Inr (i , _ , _ , i<∥rs1∥ , i<∥rs2∥ , cf) = Inr λ
            { (_ , XCExRefl) → r1≠r2 refl ;
              (_ , XCTpl {ks = ks} _ _ ∥rs1∥==∥ks∥ C<children>) →
                let _ , i<∥ks∥ = ∥l1∥==∥l2∥→l1[i]→l2[i] ∥rs1∥==∥ks∥ i<∥rs1∥ in
                cf (_ , C<children> i<∥rs1∥ i<∥rs2∥ i<∥ks∥)
            }
    constraints-dec ⟨ rs1 ⟩ ([ x ]λ x₁ => x₂) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec ⟨ rs1 ⟩ [ x ]fix x₁ ⦇·λ x₂ => x₃ ·⦈ | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec ⟨ rs1 ⟩ (C[ x ] r2) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec ⟨ rs1 ⟩ [ x ]??[ x₁ ] | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec ⟨ rs1 ⟩ (r2 ∘ r3) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec ⟨ rs1 ⟩ (get[ x th-of x₁ ] r2) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec ⟨ rs1 ⟩ [ x ]case r2 of⦃· x₁ ·⦄ | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec ⟨ rs1 ⟩ (PF x) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (C[ c1 ] r1) (C[ c2 ] r2) | Inr r1≠r2
      with constraints-dec r1 r2
    ... | Inr cf = Inr λ
            { (_ , XCExRefl)     → cf (_ , XCExRefl) ;
              (_ , XCCTor _ rec) → cf (_ , rec) }
    ... | Inl (_ , C<r1,r2>)
      with natEQ c1 c2
    ... | Inr ne = Inr λ
            { (_ , XCExRefl)   → ne refl ;
              (_ , XCCTor _ _) → ne refl }
    ... | Inl refl = Inl (_ , XCCTor r1≠r2 C<r1,r2>)
    constraints-dec (C[ c1 ] r1) ([ x ]λ x₁ => x₂) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (C[ c1 ] r1) [ x ]fix x₁ ⦇·λ x₂ => x₃ ·⦈ | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (C[ c1 ] r1) ⟨ x ⟩ | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (C[ c1 ] r1) [ x ]??[ x₁ ] | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (C[ c1 ] r1) (r2 ∘ r3) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (C[ c1 ] r1) (get[ x th-of x₁ ] r2) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (C[ c1 ] r1) [ x ]case r2 of⦃· x₁ ·⦄ | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (C[ c1 ] r1) (PF x) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (rf1 ∘ rarg1) (rf2 ∘ rarg2) | Inr r1≠r2
      with constraints-dec rf1 rf2
    ... | Inr cf = Inr λ
            { (_ , XCExRefl)     → cf (_ , XCExRefl) ;
              (_ , XCAp _ rec _) → cf (_ , rec) }
    ... | Inl (_ , C<rf1,rf2>)
      with constraints-dec rarg1 rarg2
    ... | Inr cf = Inr λ
            { (_ , XCExRefl)     → cf (_ , XCExRefl) ;
              (_ , XCAp _ _ rec) → cf (_ , rec) }
    ... | Inl (_ , C<rarg1,rarg2>) = Inl (_ , XCAp r1≠r2 C<rf1,rf2> C<rarg1,rarg2>)
    constraints-dec (rf1 ∘ rarg1) ([ x ]λ x₁ => x₂) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (rf1 ∘ rarg1) [ x ]fix x₁ ⦇·λ x₂ => x₃ ·⦈ | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (rf1 ∘ rarg1) ⟨ x ⟩ | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (rf1 ∘ rarg1) (C[ x ] r2) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (rf1 ∘ rarg1) [ x ]??[ x₁ ] | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (rf1 ∘ rarg1) (get[ x th-of x₁ ] r2) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (rf1 ∘ rarg1) [ x ]case r2 of⦃· x₁ ·⦄ | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (rf1 ∘ rarg1) (PF x) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (get[ i1 th-of n1 ] r1) (get[ i2 th-of n2 ] r2) | Inr r1≠r2
      with natEQ i1 i2
    ... | Inr ne = Inr λ
            { (_ , XCExRefl)    → ne refl ;
              (_ , XCGet _ rec) → ne refl }
    ... | Inl refl
      with natEQ n1 n2
    ... | Inr ne = Inr λ
            { (_ , XCExRefl)    → ne refl ;
              (_ , XCGet _ rec) → ne refl }
    ... | Inl refl
      with constraints-dec r1 r2
    ... | Inr cf = Inr λ
            { (_ , XCExRefl)    → cf (_ , XCExRefl) ;
              (_ , XCGet _ rec) → cf (_ , rec) }
    ... | Inl (_ , C<r1,r2>) = Inl (_ , XCGet r1≠r2 C<r1,r2>)
    constraints-dec (get[ i1 th-of n1 ] r1) ([ x ]λ x₁ => x₂) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (get[ i1 th-of n1 ] r1) [ x ]fix x₁ ⦇·λ x₂ => x₃ ·⦈ | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (get[ i1 th-of n1 ] r1) ⟨ x ⟩ | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (get[ i1 th-of n1 ] r1) (C[ x ] r2) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (get[ i1 th-of n1 ] r1) [ x ]??[ x₁ ] | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (get[ i1 th-of n1 ] r1) (r2 ∘ r3) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (get[ i1 th-of n1 ] r1) [ x ]case r2 of⦃· x₁ ·⦄ | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (get[ i1 th-of n1 ] r1) (PF x) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec [ E1 ]case r1 of⦃· rules1 ·⦄ [ E2 ]case r2 of⦃· rules2 ·⦄ | Inr r1≠r2
      with ctx<result>-==-dec E1 E2
    ... | Inr ne   = Inr λ
            { (_ , XCExRefl)      → ne refl ;
              (_ , XCMatch _ rec) → ne refl }
    ... | Inl refl
      with constraints-dec r1 r2
    ... | Inr cf = Inr λ
            { (_ , XCExRefl)      → cf (_ , XCExRefl) ;
              (_ , XCMatch _ rec) → cf (_ , rec) }
    ... | Inl (_ , C<r1,r2>)
      with ctx<rule>-==-dec rules1 rules2
    ... | Inr ne = Inr λ
            { (_ , XCExRefl)      → ne refl ;
              (_ , XCMatch _ rec) → ne refl }
    ... | Inl refl = Inl (_ , XCMatch r1≠r2 C<r1,r2>)
    constraints-dec [ E1 ]case r1 of⦃· rules1 ·⦄ ([ x ]λ x₁ => x₂) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec [ E1 ]case r1 of⦃· rules1 ·⦄ [ x ]fix x₁ ⦇·λ x₂ => x₃ ·⦈ | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec [ E1 ]case r1 of⦃· rules1 ·⦄ ⟨ x ⟩ | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec [ E1 ]case r1 of⦃· rules1 ·⦄ (C[ x ] r2) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec [ E1 ]case r1 of⦃· rules1 ·⦄ [ x ]??[ x₁ ] | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec [ E1 ]case r1 of⦃· rules1 ·⦄ (r2 ∘ r3) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec [ E1 ]case r1 of⦃· rules1 ·⦄ (get[ x th-of x₁ ] r2) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec [ E1 ]case r1 of⦃· rules1 ·⦄ (PF x) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (PF pf1) (PF pf2) | Inr r1≠r2 = Inr (λ where (_ , XCExRefl) → r1≠r2 refl)
    constraints-dec (PF pf1) ([ x ]λ x₁ => x₂) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (PF pf1) [ x ]fix x₁ ⦇·λ x₂ => x₃ ·⦈ | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (PF pf1) ⟨ x ⟩ | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (PF pf1) (C[ x ] r2) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (PF pf1) (r2 ∘ r3) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (PF pf1) (get[ x th-of x₁ ] r2) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec (PF pf1) [ x ]case r2 of⦃· x₁ ·⦄ | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec [ E1 ]??[ u1 ] [ E2 ]??[ u2 ] | Inr r1≠r2 = Inr (λ where (_ , XCExRefl) → r1≠r2 refl)
    constraints-dec [ E1 ]??[ u1 ] ([ x ]λ x₁ => x₂) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec [ E1 ]??[ u1 ] [ x ]fix x₁ ⦇·λ x₂ => x₃ ·⦈ | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec [ E1 ]??[ u1 ] ⟨ x ⟩ | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec [ E1 ]??[ u1 ] (C[ x ] r2) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec [ E1 ]??[ u1 ] (r2 ∘ r3) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec [ E1 ]??[ u1 ] (get[ x th-of x₁ ] r2) | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec [ E1 ]??[ u1 ] [ x ]case r2 of⦃· x₁ ·⦄ | Inr r1≠r2 = Inr (λ where (_ , ()))
    constraints-dec [ E1 ]??[ u1 ] (PF x) | Inr r1≠r2 = Inl (_ , XCEx)
    constraints-dec (PF pf1) [ x ]??[ x₁ ] | Inr r1≠r2 = Inl (_ , XCExSymm)

    -- lemma
    list<constraints>-dec : ∀{rs1 rs2} →
                              ∥ rs1 ∥ == ∥ rs2 ∥ →
                              Σ[ ks ∈ List constraints ]
                                 ( ∥ rs1 ∥ == ∥ ks ∥ ∧
                                   (∀{i r1-i r2-i k-i} →
                                      rs1 ⟦ i ⟧ == Some r1-i →
                                      rs2 ⟦ i ⟧ == Some r2-i →
                                      ks  ⟦ i ⟧ == Some k-i →
                                      Constraints⦃ r1-i , r2-i ⦄:= k-i)
                                 ) ∨
                              Σ[ i ∈ Nat ] Σ[ r1-i ∈ result ] Σ[ r2-i ∈ result ] (
                                 rs1 ⟦ i ⟧ == Some r1-i ∧
                                 rs2 ⟦ i ⟧ == Some r2-i ∧
                                 Constraints⦃ r1-i , r2-i ⦄:=∅)
    list<constraints>-dec {[]} {[]} ∥rs1∥==∥rs2∥ = Inl (_ , ∥rs1∥==∥rs2∥ , λ ())
    list<constraints>-dec {[]} {_ :: _} ()
    list<constraints>-dec {_ :: _} {[]} ()
    list<constraints>-dec {h1 :: t1} {h2 :: t2} ∥rs1∥==∥rs2∥
      with constraints-dec h1 h2
    ... | Inr cf = Inr (Z , h1 , h2 , refl , refl , λ {(_ , C<h1,h2>) → cf (_ , C<h1,h2>)})
    ... | Inl (hks , C<h1,h2>)
      with list<constraints>-dec {t1} {t2} (1+inj ∥rs1∥==∥rs2∥)
    ... | Inl (tks , ∥t1∥==∥tks∥ , C<t1,t2>)
            = Inl ((hks :: tks) , 1+ap ∥t1∥==∥tks∥ , λ {i} → ap-C<t1,t2> {i}) -- ← wtf?
              where
              ap-C<t1,t2> : ∀{i r1-i r2-i k-i} →
                              (h1 :: t1)   ⟦ i ⟧ == Some r1-i →
                              (h2 :: t2)   ⟦ i ⟧ == Some r2-i →
                              (hks :: tks) ⟦ i ⟧ == Some k-i →
                              Constraints⦃ r1-i , r2-i ⦄:= k-i
              ap-C<t1,t2> {Z}    rs1[i] rs2[i] ks[i]
                rewrite someinj rs1[i] | someinj rs2[i] | someinj ks[i]
                  = C<h1,h2>
              ap-C<t1,t2> {1+ i} rs1[i] rs2[i] ks[i]
                = C<t1,t2> rs1[i] rs2[i] ks[i]
    ... | Inr (j , j<∥t1∥ , j<∥t2∥ , h₁ , h₂ , cf) = Inr (1+ j , _ , _ , h₁ , h₂ , cf)
  -}
