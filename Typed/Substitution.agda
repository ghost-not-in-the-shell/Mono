module Mono.Typed.Substitution where
open import Mono.Prelude
open import Mono.Untyped.PreTerm
open import Mono.Untyped.Weakening
open import Mono.Untyped.Substitution
open import Mono.Untyped.Substitution.Properties
open import Mono.Typed.Term
open import Mono.Typed.Weakening

infix  4 _⊢⃗_∶_
infixl 5 _,_
infixr 6 _⊚_
infixr 6 _◐̅_
infixr 6 _◑̅_

data _⊢⃗_∶_ {𝔪} {Δ : Con 𝔪} (𝔻 : Δ ctx) : ∀ {𝔫} → Sub 𝔪 𝔫 → Con 𝔫 → Set where
  · : 𝔻 ⊢⃗ · ∶ ·

  _,_ : ∀ {𝔫} {Γ : Con 𝔫} {ρ : Sub 𝔪 𝔫} {A : Tm 𝔫} {t : Tm 𝔪}
    → (ℽ : 𝔻 ⊢⃗     ρ ∶ Γ)
    → (𝕥 : 𝔻 ⊢     t ∶ A [ ρ ])
    →      𝔻 ⊢⃗ ρ , t ∶ Γ , A

_◐̅_ : ∀ {𝔩 𝔪 𝔫} {Ε : Con 𝔩} {𝔼 : Ε ctx} {Δ : Con 𝔪} {Γ : Con 𝔫} {𝓌 : Ren 𝔪 𝔫} {ρ : Sub 𝔩 𝔪}
  → Δ ⊇     𝓌 ∶ Γ
  → 𝔼 ⊢⃗     ρ ∶ Δ
  → 𝔼 ⊢⃗ 𝓌 ◐ ρ ∶ Γ
𝕕𝕠𝕟𝕖        ◐̅ ·       = ·
𝕤𝕜𝕚𝕡⁽ A ⁾ 𝕨 ◐̅ (ℽ , 𝕥) = 𝕨 ◐̅ ℽ
𝕜𝕖𝕖𝕡⁽ A ⁾ 𝕨 ◐̅ (ℽ , 𝕥) = 𝕨 ◐̅ ℽ , (𝕥 ⟦ (_ ⊢ _ ∶_) ⟨$⟩ sym (sub⊢‿◐ _ _ A) ⟫)

_◑̅_ : ∀ {𝔩 𝔪 𝔫} {Ε : Con 𝔩} {𝔼 : Ε ctx} {Δ : Con 𝔪} {𝔻 : Δ ctx} {Γ : Con 𝔫} {ρ : Sub 𝔪 𝔫} {𝓌 : Ren 𝔩 𝔪}
  → 𝔻 ⊢⃗ ρ ∶ Γ
  → Ε ⊇ 𝓌 ∶ Δ
  → 𝔼 ⊢⃗ ρ ◑ 𝓌 ∶ Γ
·                 ◑̅ 𝕨 = ·
(_,_ {A = A} ℽ 𝕥) ◑̅ 𝕨 = ℽ ◑̅ 𝕨 , (𝕣𝕖𝕟⊢ 𝕨 𝕥 ⟦ (_ ⊢ _ ∶_) ⟨$⟩ sym (sub⊢‿◑ _ _ A) ⟫)

⌜𝕤𝕜𝕚𝕡⁽_⁾⌝ : ∀ {𝔪 𝔫} {Δ : Con 𝔪} {𝔻 : Δ ctx} {Γ : Con 𝔫} {ρ : Sub 𝔪 𝔫} {A : Tm 𝔪}
  → (𝔸 : 𝔻     ⊢        A ∶ U)
  → (ℽ : 𝔻     ⊢⃗        ρ ∶ Γ)
  →      𝔻 , 𝔸 ⊢⃗ ⌜skip⌝ ρ ∶ Γ
⌜𝕤𝕜𝕚𝕡⁽ 𝔸 ⁾⌝ ℽ = ℽ ◑̅ ⇑

⌜𝕤𝕜𝕚𝕡⌝ : ∀ {𝔪 𝔫} {Δ : Con 𝔪} {𝔻 : Δ ctx} {Γ : Con 𝔫} {ρ : Sub 𝔪 𝔫} {A : Tm 𝔪}
  → {𝔸 : 𝔻     ⊢        A ∶ U}
  → (ℽ : 𝔻     ⊢⃗        ρ ∶ Γ)
  →      𝔻 , 𝔸 ⊢⃗ ⌜skip⌝ ρ ∶ Γ
⌜𝕤𝕜𝕚𝕡⌝ = ⌜𝕤𝕜𝕚𝕡⁽ _ ⁾⌝

{-
⌜𝕜𝕖𝕖𝕡⌝ : ∀ {𝔪 𝔫} {Δ : Con 𝔪} {𝔻 : Δ ctx} {Γ : Con 𝔫} {𝔾 : Γ ctx} {ρ : Sub 𝔪 𝔫} {A : Tm 𝔫}
  → {𝔸 : 𝔾 ⊢ A ∶ U}
  → (ℽ : 𝔻 ⊢⃗       ρ ∶ Γ)
  →      𝔻 , sub⊢ ρ A ⊢⃗ ⌜keep⌝ ρ ∶ Γ , A
⌜𝕜𝕖𝕖𝕡⌝ = ?
-}

{-
data _⊢⃗_∶_ {𝔪} (Δ : Con 𝔪) : ∀ {𝔫} → Sub 𝔪 𝔫 → Con 𝔫 → Set where
  · : Δ ⊢⃗ · ∶ ·

  _,_ : ∀ {𝔫} {Γ : Con 𝔫} {ρ : Sub 𝔪 𝔫} {A : Tm 𝔫} {t : Tm 𝔪}
    → (ℽ : Δ ⊢⃗     ρ ∶ Γ)
    → {𝔻 : Δ ctx}
    → (𝕥 : 𝔻 ⊢     t ∶ A [ ρ ])
    →      Δ ⊢⃗ ρ , t ∶ Γ , A

_◐̅_ : ∀ {𝔩 𝔪 𝔫} {Ε : Con 𝔩} {Δ : Con 𝔪} {Γ : Con 𝔫} {𝓌 : Ren 𝔪 𝔫} {ρ : Sub 𝔩 𝔪}
  → Δ ⊇ 𝓌 ∶ Γ
  → Ε ⊢⃗ ρ ∶ Δ
  → Ε ⊢⃗ 𝓌 ◐ ρ ∶ Γ
𝕕𝕠𝕟𝕖        ◐̅ ·       = ·
𝕤𝕜𝕚𝕡      𝕨 ◐̅ (ℽ , 𝕥) = 𝕨 ◐̅ ℽ
𝕜𝕖𝕖𝕡⁽ A ⁾ 𝕨 ◐̅ (ℽ , 𝕥) = 𝕨 ◐̅ ℽ , (𝕥 ⟦ (_ ⊢ _ ∶_) ⟨$⟩ sym (sub⊢‿◐ _ _ A) ⟫)

_◑̅_ : ∀ {𝔩 𝔪 𝔫} {Ε : Con 𝔩} {Δ : Con 𝔪} {Γ : Con 𝔫} {ρ : Sub 𝔪 𝔫} {𝓌 : Ren 𝔩 𝔪}
  → Δ ⊢⃗ ρ ∶ Γ
  → Ε ⊇ 𝓌 ∶ Δ
  → Ε ⊢⃗ ρ ◑ 𝓌 ∶ Γ
·       ◑̅ 𝕨 = ·
(ℽ , 𝕥) ◑̅ 𝕨 = ℽ ◑̅ 𝕨 , (𝕣𝕖𝕟⊢ 𝕨 𝕥 ⟦ {!!} ⟫)

-}

-- (_,_ {ρ = ρ} {A} ℽ {𝔻} 𝕥) ◑̅ 𝕨 = ℽ ◑̅ 𝕨 , (𝕣𝕖𝕟⊢ 𝕨 𝕥 ⟦ {!(𝔻 ⊢ _ ∶_) ⟨$⟩ ?!} ⟫)

{-
_⊚_ : ∀ {𝔩 𝔪 𝔫} {Ε : Con 𝔩} {Δ : Con 𝔪} {Γ : Con 𝔫} {ρ₁ : Sub 𝔪 𝔫} {ρ₂ : Sub 𝔩 𝔪}
  → Δ ⊢⃗ ρ₁ ∶ Γ
  → Ε ⊢⃗ ρ₂ ∶ Δ
  → Ε ⊢⃗ ρ₁ ∘ ρ₂ ∶ Γ
ℽ₁ ⊚ ℽ₂ = {!!}
-}

