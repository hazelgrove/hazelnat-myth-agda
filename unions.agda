open import Prelude
open import Nat
open import List
open import contexts

module unions where
  -- values mapped in Γ2 replace those mapped in Γ1
  _∪_ : {A : Set} → A ctx → A ctx → A ctx
  Γ1 ∪ Γ2 = union (λ a b → b) Γ1 Γ2

  -- duplicate mappings are combined by append (_++_)
  _⊎_ : {A : Set} → (List A) ctx → (List A) ctx → (List A) ctx
  Γ1 ⊎ Γ2 = union (λ a b → a ++ b) Γ1 Γ2

  infixl 50 _∪_
  infixl 50 _⊎_
