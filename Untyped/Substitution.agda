module Mono.Untyped.Substitution where
open import Mono.Prelude
open import Mono.Untyped.PreTerm
open import Mono.Untyped.Weakening

infixl 5 _,_
infixr 6 _◐_
infixr 6 _◑_

data Sub (𝔪 : Nat) : Nat → Set where
  ·   : Sub 𝔪 zero
  _,_ : ∀ {𝔫} → Sub 𝔪 𝔫 → Tm 𝔪 → Sub 𝔪 (suc 𝔫)

_◐_ : ∀ {𝔩 𝔪 𝔫} → Ren 𝔪 𝔫 → Sub 𝔩 𝔪 → Sub 𝔩 𝔫
done   ◐ ·       = ·
skip 𝓌 ◐ (ρ , t) = 𝓌 ◐ ρ
keep 𝓌 ◐ (ρ , t) = 𝓌 ◐ ρ , t

_◑_ : ∀ {𝔩 𝔪 𝔫} → Sub 𝔪 𝔫 → Ren 𝔩 𝔪 → Sub 𝔩 𝔫
·       ◑ 𝓌 = ·
(ρ , t) ◑ 𝓌 = (ρ ◑ 𝓌) , ren⊢ 𝓌 t

⌜skip⌝ : ∀ {𝔪 𝔫} → Sub 𝔪 𝔫 → Sub (suc 𝔪) 𝔫
⌜skip⌝ ρ = ρ ◑ ↑

⌜keep⌝ : ∀ {𝔪 𝔫} → Sub 𝔪 𝔫 → Sub (suc 𝔪) (suc 𝔫)
⌜keep⌝ ρ = ⌜skip⌝ ρ , var zero

⌜_⌝ : ∀ {𝔪 𝔫} → Ren 𝔪 𝔫 → Sub 𝔪 𝔫
⌜ done   ⌝ = ·
⌜ skip 𝓌 ⌝ = ⌜skip⌝ ⌜ 𝓌 ⌝
⌜ keep 𝓌 ⌝ = ⌜keep⌝ ⌜ 𝓌 ⌝

sub∋ : ∀ {𝔪 𝔫} → Sub 𝔪 𝔫 → Var 𝔫 → Tm 𝔪
sub∋ (ρ , t) zero    = t
sub∋ (ρ , t) (suc x) = sub∋ ρ x

sub⊢ : ∀ {𝔪 𝔫} → Sub 𝔪 𝔫 → Tm 𝔫 → Tm 𝔪
sub⊢ ρ (U)       = U
sub⊢ ρ (Π A B)   = Π (sub⊢ ρ A) (sub⊢ (⌜keep⌝ ρ) B)
sub⊢ ρ (T)       = T
sub⊢ ρ (var x)   = sub∋ ρ x
sub⊢ ρ (lam t)   = lam (sub⊢ (⌜keep⌝ ρ) t)
sub⊢ ρ (app t u) = app (sub⊢ ρ t) (sub⊢ ρ u)
sub⊢ ρ (tt)      = tt

instance
  𝒞ℴ𝓃 : Category Sub
  id  ⦃ 𝒞ℴ𝓃 ⦄ = ⌜ id ⌝

  _∘_ ⦃ 𝒞ℴ𝓃 ⦄ ·        ρ₂ = ·
  _∘_ ⦃ 𝒞ℴ𝓃 ⦄ (ρ₁ , t) ρ₂ = (ρ₁ ∘ ρ₂) , sub⊢ ρ₂ t

_[_] : ∀ {𝔪 𝔫} → Tm 𝔫 → Sub 𝔪 𝔫 → Tm 𝔪
t [ ρ ] = sub⊢ ρ t

_[_]₁ : ∀ {𝔫} → Tm (suc 𝔫) → Tm 𝔫 → Tm 𝔫
t [ u ]₁ = sub⊢ (id , u) t
