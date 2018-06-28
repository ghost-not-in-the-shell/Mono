module Mono.Untyped.PreTerm where
open import Mono.Prelude

infixl 5 _,_

data Var : Nat → Set where
  zero : ∀ {𝔫}         → Var (suc 𝔫)
  suc  : ∀ {𝔫} → Var 𝔫 → Var (suc 𝔫)

data Tm (𝔫 : Nat) : Set where
  U  : Tm 𝔫
  Pi : (A : Tm 𝔫) (B : Tm (suc 𝔫)) → Tm 𝔫
  T  : Tm 𝔫

  var : (x : Var 𝔫) → Tm 𝔫
  lam : (t : Tm (suc 𝔫)) → Tm 𝔫
  app : (t u : Tm 𝔫) → Tm 𝔫

  tt : Tm 𝔫

data Con : Nat → Set where
  ·   : Con zero
  _,_ : ∀ {𝔫} → Con 𝔫 → Tm 𝔫 → Con (suc 𝔫)
