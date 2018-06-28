module Mono.Typed.Weakening where
open import Mono.Prelude
open import Mono.Untyped.PreTerm
open import Mono.Untyped.Weakening
open import Mono.Untyped.Weakening.Properties
open import Mono.Untyped.Substitution
open import Mono.Untyped.Substitution.Properties
open import Mono.Typed.Term

infix 4 _⊇_∶_

mutual
  data _⊇_∶_ : ∀ {𝔪 𝔫} {Δ : Con 𝔪} {Γ : Con 𝔫} (𝔻 : Δ ctx) (𝓌 : Ren 𝔪 𝔫) (𝔾 : Γ ctx) → Set where
    𝕕𝕠𝕟𝕖 : · ⊇ done ∶ ·

    𝕤𝕜𝕚𝕡 : ∀ {𝔪} {Δ : Con 𝔪} {𝔻 : Δ ctx}
             {𝔫} {Γ : Con 𝔫} {𝔾 : Γ ctx}
             {𝓌 : Ren 𝔪 𝔫} {A : Tm 𝔫} {𝔸 : 𝔾 ⊢ A ∶ U}
           → (𝕨 : 𝔻             ⊇      𝓌 ∶ 𝔾)
           →      𝔻 , 𝕣𝕖𝕟⊢ 𝕨 𝔸  ⊇ skip 𝓌 ∶ 𝔾

    𝕜𝕖𝕖𝕡 : ∀ {𝔪} {Δ : Con 𝔪} {𝔻 : Δ ctx}
             {𝔫} {Γ : Con 𝔫} {𝔾 : Γ ctx}
             {𝓌 : Ren 𝔪 𝔫} {A : Tm 𝔫} {𝔸 : 𝔾 ⊢ A ∶ U}
           → (𝕨 : 𝔻            ⊇      𝓌 ∶ 𝔾)
           →      𝔻 , 𝕣𝕖𝕟⊢ 𝕨 𝔸 ⊇ keep 𝓌 ∶ 𝔾 , 𝔸

  𝕣𝕖𝕟∋ : ∀ {𝔪} {Δ : Con 𝔪} {𝔻 : Δ ctx}
           {𝔫} {Γ : Con 𝔫} {𝔾 : Γ ctx}
           {𝓌 : Ren 𝔪 𝔫} {A : Tm 𝔫} {x : Var 𝔫}
         → 𝔻 ⊇        𝓌 ∶ 𝔾
         → Γ ∋        x ∶ A
         → Δ ∋ ren∋ 𝓌 x ∶ ren⊢ 𝓌 A
  𝕣𝕖𝕟∋          𝕕𝕠𝕟𝕖    ()
  𝕣𝕖𝕟∋ {Δ = Δ} (𝕤𝕜𝕚𝕡 𝕨) 𝕩       = 𝕤𝕦𝕔 (𝕣𝕖𝕟∋ 𝕨 𝕩) ⟦ Δ ∋ _ ∶_ ⟨$⟩ ren⊢‿skip ⟫
  𝕣𝕖𝕟∋ {Δ = Δ} (𝕜𝕖𝕖𝕡 𝕨) 𝕫𝕖𝕣𝕠    = 𝕫𝕖𝕣𝕠           ⟦ Δ ∋ _ ∶_ ⟨$⟩ ren⊢‿keep ⟫
  𝕣𝕖𝕟∋ {Δ = Δ} (𝕜𝕖𝕖𝕡 𝕨) (𝕤𝕦𝕔 𝕩) = 𝕤𝕦𝕔 (𝕣𝕖𝕟∋ 𝕨 𝕩) ⟦ Δ ∋ _ ∶_ ⟨$⟩ ren⊢‿keep ⟫

  𝕣𝕖𝕟⊢ : ∀ {𝔪} {Δ : Con 𝔪} {𝔻 : Δ ctx}
           {𝔫} {Γ : Con 𝔫} {𝔾 : Γ ctx}
           {𝓌 : Ren 𝔪 𝔫} {A : Tm 𝔫} {t : Tm 𝔫}
         → 𝔻 ⊇        𝓌 ∶ 𝔾
         → 𝔾 ⊢        t ∶ A
         → 𝔻 ⊢ ren⊢ 𝓌 t ∶ ren⊢ 𝓌 A
  𝕣𝕖𝕟⊢ 𝕨 (𝕌)               = 𝕌
  𝕣𝕖𝕟⊢ 𝕨 (ℙ𝕚 𝔸 𝔹)          = ℙ𝕚 (𝕣𝕖𝕟⊢ 𝕨 𝔸) (𝕣𝕖𝕟⊢ (𝕜𝕖𝕖𝕡 𝕨) 𝔹)
  𝕣𝕖𝕟⊢ 𝕨 (𝕋)               = 𝕋
  𝕣𝕖𝕟⊢ 𝕨 (𝕧𝕒𝕣 𝕩)           = 𝕧𝕒𝕣 (𝕣𝕖𝕟∋ 𝕨 𝕩)
  𝕣𝕖𝕟⊢ 𝕨 (𝕝𝕒𝕞 𝕥)           = 𝕝𝕒𝕞 (𝕣𝕖𝕟⊢ (𝕜𝕖𝕖𝕡 𝕨) 𝕥)
  𝕣𝕖𝕟⊢ 𝕨 (𝕒𝕡𝕡 {B = B} 𝕥 𝕦) = 𝕒𝕡𝕡 (𝕣𝕖𝕟⊢ 𝕨 𝕥) (𝕣𝕖𝕟⊢ 𝕨 𝕦) ⟦ _ ⊢ _ ∶_ ⟨$⟩ sym (ren⊢‿sub₁ B) ⟫
  𝕣𝕖𝕟⊢ 𝕨 (𝕥𝕥)              = 𝕥𝕥
  𝕣𝕖𝕟⊢ 𝕨 (𝕥 ≫ ℍ)           = 𝕣𝕖𝕟⊢ 𝕨 𝕥 ≫ 𝕣𝕖𝕟∼ 𝕨 ℍ

  𝕣𝕖𝕟∼ : ∀ {𝔪} {Δ : Con 𝔪} {𝔻 : Δ ctx}
           {𝔫} {Γ : Con 𝔫} {𝔾 : Γ ctx}
           {𝓌 : Ren 𝔪 𝔫} {A : Tm 𝔫} {t₁ t₂ : Tm 𝔫}
         → 𝔻 ⊇                     𝓌 ∶ 𝔾
         → 𝔾 ⊢        t₁ ∼        t₂ ∶ A
         → 𝔻 ⊢ ren⊢ 𝓌 t₁ ∼ ren⊢ 𝓌 t₂ ∶ ren⊢ 𝓌 A
  𝕣𝕖𝕟∼ 𝕨 (𝕣𝕖𝕗𝕝  𝕥)                 = 𝕣𝕖𝕗𝕝  (𝕣𝕖𝕟⊢ 𝕨 𝕥)
  𝕣𝕖𝕟∼ 𝕨 (𝕤𝕪𝕞   𝕡)                 = 𝕤𝕪𝕞   (𝕣𝕖𝕟∼ 𝕨 𝕡)
  𝕣𝕖𝕟∼ 𝕨 (𝕥𝕣𝕒𝕟𝕤 𝕡 𝕢)               = 𝕥𝕣𝕒𝕟𝕤 (𝕣𝕖𝕟∼ 𝕨 𝕡) (𝕣𝕖𝕟∼ 𝕨 𝕢)
  𝕣𝕖𝕟∼ 𝕨 (ℙ𝕚-𝕔𝕠𝕟𝕘 ℍ₁ ℍ₂)           = ℙ𝕚-𝕔𝕠𝕟𝕘 (𝕣𝕖𝕟∼ 𝕨 ℍ₁) (𝕣𝕖𝕟∼ (𝕜𝕖𝕖𝕡 𝕨) ℍ₂)
  𝕣𝕖𝕟∼ 𝕨 (𝕝𝕒𝕞-𝕔𝕠𝕟𝕘 𝕡)              = 𝕝𝕒𝕞-𝕔𝕠𝕟𝕘 (𝕣𝕖𝕟∼ (𝕜𝕖𝕖𝕡 𝕨) 𝕡)
  𝕣𝕖𝕟∼ 𝕨 (𝕒𝕡𝕡-𝕔𝕠𝕟𝕘 {B = B} 𝕡 𝕢)    = 𝕒𝕡𝕡-𝕔𝕠𝕟𝕘 (𝕣𝕖𝕟∼ 𝕨 𝕡) (𝕣𝕖𝕟∼ 𝕨 𝕢) ⟦ _ ⊢ _ ∼ _ ∶_ ⟨$⟩ sym (ren⊢‿sub₁ B) ⟫
  𝕣𝕖𝕟∼ 𝕨 (ℙ𝕚-𝕓𝕖𝕥𝕒 {B = B} {t} 𝕥 𝕦) = ℙ𝕚-𝕓𝕖𝕥𝕒 (𝕣𝕖𝕟⊢ (𝕜𝕖𝕖𝕡 𝕨) 𝕥) (𝕣𝕖𝕟⊢ 𝕨 𝕦) ⟦ _ ⊢ app _ _ ∼_∶_ ⟨$⟩ sym (ren⊢‿sub₁ t) ⟨*⟩ sym (ren⊢‿sub₁ B) ⟫
  𝕣𝕖𝕟∼ 𝕨 (ℙ𝕚-𝕖𝕥𝕒 𝕥)                = ℙ𝕚-𝕖𝕥𝕒 (𝕣𝕖𝕟⊢ 𝕨 𝕥) ⟦ (λ u → _ ⊢ ren⊢ _ _ ∼ lam (app u (var zero)) ∶ _) ⟨$⟩ ren⊢‿keep ⟫
  𝕣𝕖𝕟∼ 𝕨 (𝕡 ≫ ℍ)                   = 𝕣𝕖𝕟∼ 𝕨 𝕡 ≫ 𝕣𝕖𝕟∼ 𝕨 ℍ

mutual
  𝕚𝕕 : ∀ {𝔫} {Γ : Con 𝔫} {ℾ : Γ ctx}
    → ℾ ⊇ id ∶ ℾ
  𝕚𝕕 {ℾ = ·}     = 𝕕𝕠𝕟𝕖
  𝕚𝕕 {ℾ = ℾ , 𝔸} = {!𝕜𝕖𝕖𝕡 𝕚𝕕 ⟦ (λ 𝔹 → ℾ , 𝔹 ⊇ keep id ∶ ℾ , 𝔸) ⟨$⟩ ? ⟫!}

  𝕣𝕖𝕟∋-𝕚𝕕 : ∀ {𝔫} {Γ : Con 𝔫} {𝔾 : Γ ctx} {A : Tm 𝔫} {x : Var 𝔫}
    → (𝕩 : Γ ∋ x ∶ A)
    → 𝕣𝕖𝕟∋ 𝕚𝕕 𝕩 ≡ 𝕩 ⟦ Γ ∋_∶_ ⟨$⟩ sym (ren∋-id x) ⟨*⟩ sym (ren⊢‿id A) ⟫
  𝕣𝕖𝕟∋-𝕚𝕕 𝕫𝕖𝕣𝕠    = {!!}
  𝕣𝕖𝕟∋-𝕚𝕕 (𝕤𝕦𝕔 𝕩) = {!!}

  𝕣𝕖𝕟⊢‿𝕚𝕕 : ∀ {𝔫} {Γ : Con 𝔫} {ℾ : Γ ctx} {A : Tm 𝔫} {t : Tm 𝔫}
    → (𝕥 : ℾ ⊢ t ∶ A)
    → 𝕣𝕖𝕟⊢ 𝕚𝕕 𝕥 ≡ 𝕥 ⟦ ℾ ⊢_∶_ ⟨$⟩ sym (ren⊢‿id t) ⟨*⟩ sym (ren⊢‿id A) ⟫
  𝕣𝕖𝕟⊢‿𝕚𝕕 𝕥 = {!!}