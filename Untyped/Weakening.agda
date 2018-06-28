module Mono.Untyped.Weakening where
open import Mono.Prelude
open import Mono.Untyped.PreTerm

infixr 6 _∙_

data Ren : Nat → Nat → Set where
  done : Ren zero zero
  skip : ∀ {𝔪 𝔫} → Ren 𝔪 𝔫 → Ren (suc 𝔪)      𝔫
  keep : ∀ {𝔪 𝔫} → Ren 𝔪 𝔫 → Ren (suc 𝔪) (suc 𝔫)

instance
  𝒪𝒫ℰ : Category Ren
  id  ⦃ 𝒪𝒫ℰ ⦄ {zero}  = done
  id  ⦃ 𝒪𝒫ℰ ⦄ {suc 𝔫} = keep id

  _∘_ ⦃ 𝒪𝒫ℰ ⦄       𝓌₁   done     = 𝓌₁
  _∘_ ⦃ 𝒪𝒫ℰ ⦄       𝓌₁  (skip 𝓌₂) = skip (𝓌₁ ∘ 𝓌₂)
  _∘_ ⦃ 𝒪𝒫ℰ ⦄ (skip 𝓌₁) (keep 𝓌₂) = skip (𝓌₁ ∘ 𝓌₂)
  _∘_ ⦃ 𝒪𝒫ℰ ⦄ (keep 𝓌₁) (keep 𝓌₂) = keep (𝓌₁ ∘ 𝓌₂)

_∙_ = _∘_

↑ : ∀ {𝔫} → Ren (suc 𝔫) 𝔫
↑ = skip id

ren∋ : ∀ {𝔪 𝔫} → Ren 𝔪 𝔫 → Var 𝔫 → Var 𝔪
ren∋  done    ()
ren∋ (skip 𝓌) x       = suc (ren∋ 𝓌 x)
ren∋ (keep 𝓌) zero    = zero
ren∋ (keep 𝓌) (suc x) = suc (ren∋ 𝓌 x)

ren⊢ : ∀ {𝔪 𝔫} → Ren 𝔪 𝔫 → Tm 𝔫 → Tm 𝔪
ren⊢ 𝓌 (U)       = U
ren⊢ 𝓌 (Pi A B)  = Pi (ren⊢ 𝓌 A) (ren⊢ (keep 𝓌) B)
ren⊢ 𝓌 (T)       = T
ren⊢ 𝓌 (var x)   = var (ren∋ 𝓌 x)
ren⊢ 𝓌 (lam t)   = lam (ren⊢ (keep 𝓌) t)
ren⊢ 𝓌 (app t u) = app (ren⊢ 𝓌 t) (ren⊢ 𝓌 u)
ren⊢ 𝓌 (tt)      = tt

_[↑] : ∀ {𝔫} → Tm 𝔫 → Tm (suc 𝔫)
t [↑] = ren⊢ ↑ t
