open import Nat
open import Prelude
open import List

open import contexts
open import core

module lemmas-general where
  Coerce-unicity : ∀{r ex1 ex2} →
                     Coerce r := ex1 →
                     Coerce r := ex2 →
                     ex1 == ex2
  Coerce-unicity CoerceUnit CoerceUnit = refl
  Coerce-unicity (CoercePair C1 C2) (CoercePair C3 C4)
    rewrite Coerce-unicity C1 C3 | Coerce-unicity C2 C4
      = refl
  Coerce-unicity (CoerceCtor C1) (CoerceCtor C2)
    rewrite Coerce-unicity C1 C2
      = refl

  Fuel-depletion-unicity : ∀{⛽ ⛽↓1 ⛽↓2} →
                             ⛽ ⛽⇓ ⛽↓1 →
                             ⛽ ⛽⇓ ⛽↓2 →
                             ⛽↓1 == ⛽↓2
  Fuel-depletion-unicity CF∞ CF∞ = refl
  Fuel-depletion-unicity CF⛽ CF⛽ = refl
