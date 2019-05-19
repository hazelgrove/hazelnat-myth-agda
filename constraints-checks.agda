open import Nat
open import Prelude
open import List

open import contexts
open import core

module constraints-checks where
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
  constraints-unicity (XCTpl {ks = ks1} _ ∥rs1⊫=∥rs2∥ ∥rs1⊫=∥ks1∥ h1) (XCTpl {ks = ks2} _ _ ∥rs1⊫=∥ks2∥ h2)
    rewrite
      ==comm
        (! ∥rs1⊫=∥ks1∥ · ∥rs1⊫=∥ks2∥)
        (λ {i} i<∥l1∥ i<∥l2∥ →
           let
             i<∥rs1∥ = tr (λ y → i < y) (! ∥rs1⊫=∥ks1∥) i<∥l1∥
             i<∥rs2∥ = tr (λ y → i < y) ∥rs1⊫=∥rs2∥ i<∥rs1∥
           in
           constraints-unicity (h1 i<∥rs1∥ i<∥rs2∥ i<∥l1∥) (h2 i<∥rs1∥ i<∥rs2∥ i<∥l2∥))
    = refl
  constraints-unicity (XCCTor ne _) XCExRefl = abort (ne refl)
  constraints-unicity (XCCTor _ :=k) (XCCTor _ :=k') = constraints-unicity :=k :=k'
  constraints-unicity (XCAp ne _ _) XCExRefl = abort (ne refl)
  constraints-unicity (XCAp _ :=kf :=karg) (XCAp _ :=kf' :=karg')
    rewrite constraints-unicity :=kf' :=kf | constraints-unicity :=karg :=karg' = refl
  constraints-unicity (XCGet ne _) XCExRefl = abort (ne refl)
  constraints-unicity (XCGet _ :=k) (XCGet _ :=k') = constraints-unicity :=k :=k'
  constraints-unicity (XCMatch ne _) XCExRefl = abort (ne refl)
  constraints-unicity (XCMatch _ :=k) (XCMatch _ :=k') = constraints-unicity :=k :=k'

  {- TODO : Necessary for progress
  constraints-dec : (r1 r2 : result) →
                    Σ[ k ∈ constraints ] Constraints⦃ r1 , r2 ⦄:= k ∨
                    Constraints⦃ r1 , r2 ⦄:=∅
  constraints-dec ([ E ]λ x => e) r2 = {!!}
  constraints-dec [ E ]fix f ⦇·λ x => e ·⦈ r2 = {!!}
  constraints-dec ⟨ rs1 ⟩ r2 = {!!}
  constraints-dec (C[ c ] r1) r2 = {!!}
  constraints-dec [ E ]??[ u1 ] r2 = {!!}
  constraints-dec (rf1 ∘ rarg1) r2 = {!!}
  constraints-dec (get[ i th-of n ] r1) r2 = {!!}
  constraints-dec [ E ]case r1 of⦃· rules1 ·⦄ r2 = {!!}
  constraints-dec (PF pf) r2 = {!!}
  -}
