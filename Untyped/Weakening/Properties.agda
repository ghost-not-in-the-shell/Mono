module Mono.Untyped.Weakening.Properties where
open import Mono.Prelude
open import Mono.Untyped.PreTerm
open import Mono.Untyped.Weakening

∙-unitˡ : ∀ {𝔪 𝔫} (𝓌 : Ren 𝔪 𝔫) → id ∙ 𝓌 ≡ 𝓌
∙-unitˡ  done    = refl
∙-unitˡ (skip 𝓌) = skip ⟨$⟩ ∙-unitˡ 𝓌
∙-unitˡ (keep 𝓌) = keep ⟨$⟩ ∙-unitˡ 𝓌

∙-unitʳ : ∀ {𝔪 𝔫} (𝓌 : Ren 𝔪 𝔫) → 𝓌 ∙ id ≡ 𝓌
∙-unitʳ  done    = refl
∙-unitʳ (skip 𝓌) = skip ⟨$⟩ ∙-unitʳ 𝓌
∙-unitʳ (keep 𝓌) = keep ⟨$⟩ ∙-unitʳ 𝓌

∙-assoc : ∀ {𝔩 𝔪 𝔫 𝔬} (𝓌₁ : Ren 𝔫 𝔬) (𝓌₂ : Ren 𝔪 𝔫) (𝓌₃ : Ren 𝔩 𝔪) → (𝓌₁ ∙ 𝓌₂) ∙ 𝓌₃ ≡ 𝓌₁ ∙ (𝓌₂ ∙ 𝓌₃)
∙-assoc       𝓌₁        𝓌₂   done     = refl
∙-assoc       𝓌₁        𝓌₂  (skip 𝓌₃) = skip ⟨$⟩ ∙-assoc 𝓌₁ 𝓌₂ 𝓌₃
∙-assoc       𝓌₁  (skip 𝓌₂) (keep 𝓌₃) = skip ⟨$⟩ ∙-assoc 𝓌₁ 𝓌₂ 𝓌₃
∙-assoc (skip 𝓌₁) (keep 𝓌₂) (keep 𝓌₃) = skip ⟨$⟩ ∙-assoc 𝓌₁ 𝓌₂ 𝓌₃
∙-assoc (keep 𝓌₁) (keep 𝓌₂) (keep 𝓌₃) = keep ⟨$⟩ ∙-assoc 𝓌₁ 𝓌₂ 𝓌₃

ren∋-id : ∀ {𝔫} (x : Var 𝔫) → ren∋ id x ≡ x
ren∋-id zero    = refl
ren∋-id (suc x) = suc ⟨$⟩ ren∋-id x

ren∋-∙ : ∀ {𝔩 𝔪 𝔫} (𝓌₁ : Ren 𝔪 𝔫) (𝓌₂ : Ren 𝔩 𝔪) (x : Var 𝔫) → ren∋ (𝓌₁ ∙ 𝓌₂) x ≡ ren∋ 𝓌₂ (ren∋ 𝓌₁ x)
ren∋-∙  done      done     ()
ren∋-∙       𝓌₁  (skip 𝓌₂) x       = suc ⟨$⟩ ren∋-∙ 𝓌₁ 𝓌₂ x
ren∋-∙ (skip 𝓌₁) (keep 𝓌₂) x       = suc ⟨$⟩ ren∋-∙ 𝓌₁ 𝓌₂ x
ren∋-∙ (keep 𝓌₁) (keep 𝓌₂) zero    = refl
ren∋-∙ (keep 𝓌₁) (keep 𝓌₂) (suc x) = suc ⟨$⟩ ren∋-∙ 𝓌₁ 𝓌₂ x

ren⊢‿id : ∀ {𝔫} (t : Tm 𝔫) → ren⊢ id t ≡ t
ren⊢‿id (U)       = refl
ren⊢‿id (Π A B)   = Π ⟨$⟩ ren⊢‿id A ⟨*⟩ ren⊢‿id B
ren⊢‿id (T)       = refl
ren⊢‿id (var x)   = var ⟨$⟩ ren∋-id x
ren⊢‿id (lam t)   = lam ⟨$⟩ ren⊢‿id t
ren⊢‿id (app t u) = app ⟨$⟩ ren⊢‿id t ⟨*⟩ ren⊢‿id u
ren⊢‿id (tt)      = refl

ren⊢‿∙ : ∀ {𝔩 𝔪 𝔫} (𝓌₁ : Ren 𝔪 𝔫) (𝓌₂ : Ren 𝔩 𝔪) (t : Tm 𝔫) → ren⊢ (𝓌₁ ∙ 𝓌₂) t ≡ ren⊢ 𝓌₂ (ren⊢ 𝓌₁ t)
ren⊢‿∙ 𝓌₁ 𝓌₂ (U)       = refl
ren⊢‿∙ 𝓌₁ 𝓌₂ (Π A B)   = Π ⟨$⟩ ren⊢‿∙ 𝓌₁ 𝓌₂ A ⟨*⟩ ren⊢‿∙ (keep 𝓌₁) (keep 𝓌₂) B
ren⊢‿∙ 𝓌₁ 𝓌₂ (T)       = refl
ren⊢‿∙ 𝓌₁ 𝓌₂ (var x)   = var ⟨$⟩ ren∋-∙ 𝓌₁ 𝓌₂ x
ren⊢‿∙ 𝓌₁ 𝓌₂ (lam t)   = lam ⟨$⟩ ren⊢‿∙ (keep 𝓌₁) (keep 𝓌₂) t
ren⊢‿∙ 𝓌₁ 𝓌₂ (app t u) = app ⟨$⟩ ren⊢‿∙ 𝓌₁ 𝓌₂ t ⟨*⟩ ren⊢‿∙ 𝓌₁ 𝓌₂ u
ren⊢‿∙ 𝓌₁ 𝓌₂ (tt)      = refl

ren⊢‿skip : ∀ {𝔪 𝔫} {𝓌 : Ren 𝔪 𝔫} {t : Tm 𝔫}
  → ren⊢ ↑ (ren⊢ 𝓌 t) ≡ ren⊢ (skip 𝓌) t
ren⊢‿skip {𝓌 = 𝓌} {t} = begin
  ren⊢ ↑ (ren⊢ 𝓌 t)  ↑⟨ ren⊢‿∙ 𝓌 ↑ t ⟩
  ren⊢ (𝓌 ∙ ↑) t     ↓⟨ ren⊢ ⟨$⟩ (skip ⟨$⟩ ∙-unitʳ 𝓌) ⟨*⟩ refl ⟩
  ren⊢ (skip 𝓌) t    ∎

ren⊢‿keep : ∀ {𝔪 𝔫} {𝓌 : Ren 𝔪 𝔫} {t : Tm 𝔫}
  → ren⊢ ↑ (ren⊢ 𝓌 t) ≡ ren⊢ (keep 𝓌) (t [↑])
ren⊢‿keep {𝓌 = 𝓌} {t} = begin
  ren⊢ ↑ (ren⊢ 𝓌 t)      ↓⟨ ren⊢‿skip ⟩
  ren⊢ (skip 𝓌) t        ↑⟨ ren⊢ ⟨$⟩ (skip ⟨$⟩ ∙-unitˡ 𝓌) ⟨*⟩ refl ⟩
  ren⊢ (↑ ∙ keep 𝓌) t    ↓⟨ ren⊢‿∙ ↑ (keep 𝓌) t ⟩
  ren⊢ (keep 𝓌) (t [↑])  ∎
