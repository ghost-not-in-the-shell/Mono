module Mono.Typed.Term.SyntacticValidity where
open import Mono.Prelude
open import Mono.Untyped.PreTerm
open import Mono.Untyped.Weakening
open import Mono.Untyped.Substitution
open import Mono.Typed.Term
open import Mono.Typed.Weakening

infix 4 _⊢_

𝕝𝕠𝕠𝕜𝕦𝕡 : ∀ {𝔫} {Γ : Con 𝔫} {A x}
  → (𝕩 : Γ ∋ x ∶ A)
  → (𝔾 : Γ ctx)
  →      𝔾 ⊢ A ∶ U
𝕝𝕠𝕠𝕜𝕦𝕡 𝕫𝕖𝕣𝕠    (𝔾 , 𝔸) = 𝔸 ⟦⇑⟧
𝕝𝕠𝕠𝕜𝕦𝕡 (𝕤𝕦𝕔 𝕩) (𝔾 , 𝔸) = 𝕝𝕠𝕠𝕜𝕦𝕡 𝕩 𝔾 ⟦⇑⟧

mutual
  _⊢_ : ∀ {𝔫} {Γ : Con 𝔫} {A t}
    → (𝔾 : Γ ctx)
    → (𝕥 : 𝔾 ⊢ t ∶ A)
    →      𝔾 ⊢ A ∶ U
  𝔾 ⊢ 𝕌       = 𝕌
  𝔾 ⊢ ℿ 𝔸 𝔹   = 𝕌
  𝔾 ⊢ 𝕋       = 𝕌
  𝔾 ⊢ 𝕧𝕒𝕣 𝕩   = 𝕝𝕠𝕠𝕜𝕦𝕡 𝕩 𝔾
  𝔾 ⊢ 𝕝𝕒𝕞 𝕥   = ℿ _ (𝔾 , _ ⊢ 𝕥)
  𝔾 ⊢ 𝕒𝕡𝕡 𝕥 𝕦 = {!!}
  𝔾 ⊢ 𝕥𝕥      = 𝕋
  𝔾 ⊢ 𝕥 ≫ ℍ   = ∼₂ ℍ

  ∼₁ : ∀ {𝔫} {Γ : Con 𝔫} {𝔾 : Γ ctx} {A t₁ t₂}
    → 𝔾 ⊢ t₁ ∼ t₂ ∶ A
    → 𝔾 ⊢      t₁ ∶ A
  ∼₁ (𝕣𝕖𝕗𝕝  𝕥)      = 𝕥
  ∼₁ (𝕤𝕪𝕞   𝕡)      = ∼₂ 𝕡
  ∼₁ (𝕥𝕣𝕒𝕟𝕤 𝕡 𝕢)    = ∼₁ 𝕡
  ∼₁ (ℿ-𝕔𝕠𝕟𝕘 ℍ₁ ℍ₂) = ℿ _ (∼₁ ℍ₂)
  ∼₁ (𝕝𝕒𝕞-𝕔𝕠𝕟𝕘 𝕡)   = 𝕝𝕒𝕞 (∼₁ 𝕡)
  ∼₁ (𝕒𝕡𝕡-𝕔𝕠𝕟𝕘 𝕡 𝕢) = {!!}
  ∼₁ (ℿ-𝕓𝕖𝕥𝕒 𝕥 𝕦)   = {!!}
  ∼₁ (ℿ-𝕖𝕥𝕒 𝕥)      = 𝕥
  ∼₁ (𝕡 ≫ ℍ)        = ∼₁ 𝕡 ≫ ℍ

  ∼₂ : ∀ {𝔫} {Γ : Con 𝔫} {𝔾 : Γ ctx} {A t₁ t₂}
    → 𝔾 ⊢ t₁ ∼ t₂ ∶ A
    → 𝔾 ⊢      t₂ ∶ A
  ∼₂ (𝕣𝕖𝕗𝕝  𝕥)      = 𝕥
  ∼₂ (𝕤𝕪𝕞   𝕡)      = ∼₁ 𝕡
  ∼₂ (𝕥𝕣𝕒𝕟𝕤 𝕡 𝕢)    = ∼₂ 𝕢
  ∼₂ (ℿ-𝕔𝕠𝕟𝕘 ℍ₁ ℍ₂) = {!ℿ _ (∼₂ ℍ₂)!}
  ∼₂ (𝕝𝕒𝕞-𝕔𝕠𝕟𝕘 𝕡)   = 𝕝𝕒𝕞 (∼₂ 𝕡)
  ∼₂ (𝕒𝕡𝕡-𝕔𝕠𝕟𝕘 𝕡 𝕢) = {!!}
  ∼₂ (ℿ-𝕓𝕖𝕥𝕒 𝕥 𝕦)   = {!!}
  ∼₂ (ℿ-𝕖𝕥𝕒 𝕥)      = {!!}
  ∼₂ (𝕡 ≫ ℍ)        = ∼₂ 𝕡 ≫ ℍ
