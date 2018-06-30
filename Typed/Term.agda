module Mono.Typed.Term where
open import Mono.Untyped.PreTerm
open import Mono.Untyped.Weakening
open import Mono.Untyped.Substitution

infix 4 _ctx
infix 4 _∋_∶_
infix 4 _⊢_∶_
infix 4 _⊢_∼_∶_

data _∋_∶_ : ∀ {𝔫} → Con 𝔫 → Var 𝔫 → Tm 𝔫 → Set where
  𝕫𝕖𝕣𝕠 : ∀ {𝔫} {Γ : Con 𝔫} {A : Tm 𝔫}
    → Γ , A ∋ zero ∶ A [↑]

  𝕤𝕦𝕔 : ∀ {𝔫} {Γ : Con 𝔫} {A B : Tm 𝔫} {x : Var 𝔫}
    → Γ     ∋     x ∶ A
    → Γ , B ∋ suc x ∶ A [↑]

mutual
  data _ctx : ∀ {𝔫} → Con 𝔫 → Set where
    · : · ctx

    _,_ : ∀ {𝔫} {Γ : Con 𝔫} {A : Tm 𝔫}
      → (𝔾 : Γ ctx)
      → (𝔸 : 𝔾 ⊢ A ∶ U)
      →      Γ , A ctx

  data _⊢_∶_ {𝔫} {Γ : Con 𝔫} (𝔾 : Γ ctx) : Tm 𝔫 → Tm 𝔫 → Set where
    𝕌 : 𝔾 ⊢ U ∶ U

    ℿ : ∀ {A B}
      → (𝔸 : 𝔾     ⊢     A ∶ U)
      → (𝔹 : 𝔾 , 𝔸 ⊢     B ∶ U)
      →      𝔾     ⊢ Π A B ∶ U

    𝕋 : 𝔾 ⊢ T ∶ U

    𝕧𝕒𝕣 : ∀ {A x}
      → (𝕩 : Γ ∋     x ∶ A)
      →      𝔾 ⊢ var x ∶ A

    𝕝𝕒𝕞 : ∀ {A B t}
      → {𝔸 : 𝔾     ⊢     A ∶ U}
      → (𝕥 : 𝔾 , 𝔸 ⊢     t ∶ B)
      →      𝔾     ⊢ lam t ∶ Π A B

    𝕒𝕡𝕡 : ∀ {A B t u}
      → (𝕥 : 𝔾 ⊢       t ∶ Π A B)
      → (𝕦 : 𝔾 ⊢       u ∶ A)
      →      𝔾 ⊢ app t u ∶ B [ u ]₁

    𝕥𝕥 : 𝔾 ⊢ tt ∶ T

    _≫_ : ∀ {A B t}
      → (𝕥 : 𝔾 ⊢     t ∶ A)
      → (ℍ : 𝔾 ⊢ A ∼ B ∶ U)
      →      𝔾 ⊢     t ∶ B

  data _⊢_∼_∶_ {𝔫} {Γ : Con 𝔫} (𝔾 : Γ ctx) : Tm 𝔫 → Tm 𝔫 → Tm 𝔫 → Set where
    𝕣𝕖𝕗𝕝 : ∀ {A t}
      → (𝕥 : 𝔾 ⊢     t ∶ A)
      →      𝔾 ⊢ t ∼ t ∶ A

    𝕤𝕪𝕞 : ∀ {A t₁ t₂}
      → (𝕡 : 𝔾 ⊢ t₁ ∼ t₂ ∶ A)
      →      𝔾 ⊢ t₂ ∼ t₁ ∶ A

    𝕥𝕣𝕒𝕟𝕤 : ∀ {A t₁ t₂ t₃}
      → (𝕡 : 𝔾 ⊢ t₁ ∼ t₂ ∶ A)
      → (𝕢 : 𝔾 ⊢ t₂ ∼ t₃ ∶ A)
      →      𝔾 ⊢ t₁ ∼ t₃ ∶ A

    ℿ-𝕔𝕠𝕟𝕘 : ∀ {A₁ A₂ B₁ B₂}
      → {𝔸₁ : 𝔾      ⊢                A₁ ∶ U}
      → (ℍ₁ : 𝔾      ⊢      A₁ ∼      A₂ ∶ U)
      → (ℍ₂ : 𝔾 , 𝔸₁ ⊢      B₁ ∼      B₂ ∶ U)
      →       𝔾      ⊢ Π A₁ B₁ ∼ Π A₂ B₂ ∶ U

    𝕝𝕒𝕞-𝕔𝕠𝕟𝕘 : ∀ {A B t₁ t₂}
      → {𝔸 : 𝔾     ⊢               A ∶ U}
      → (𝕡 : 𝔾 , 𝔸 ⊢     t₁ ∼     t₂ ∶ B)
      →      𝔾     ⊢ lam t₁ ∼ lam t₂ ∶ Π A B

    𝕒𝕡𝕡-𝕔𝕠𝕟𝕘 : ∀ {A B t₁ t₂ u₁ u₂}
      → (𝕡 : 𝔾 ⊢        t₁ ∼        t₂ ∶ Π A B)
      → (𝕢 : 𝔾 ⊢        u₁ ∼        u₂ ∶ A)
      →      𝔾 ⊢ app t₁ u₁ ∼ app t₂ u₂ ∶ B [ t₁ ]₁

    ℿ-𝕓𝕖𝕥𝕒 : ∀ {A B t u}
      → {𝔸 : 𝔾     ⊢                        A ∶ U}
      → (𝕥 : 𝔾 , 𝔸 ⊢                        t ∶ B)
      → (𝕦 : 𝔾     ⊢                        u ∶ A)
      →      𝔾     ⊢ app (lam t) u ∼ t [ u ]₁ ∶ B [ u ]₁

    ℿ-𝕖𝕥𝕒 : ∀ {A B t}
      → (𝕥 : 𝔾 ⊢                                t ∶ Π A B)
      →      𝔾 ⊢ t ∼ lam (app (t [↑]) (var zero)) ∶ Π A B

    _≫_ : ∀ {A B t₁ t₂}
      → (𝕡 : 𝔾 ⊢ t₁ ∼ t₂ ∶ A)
      → (ℍ : 𝔾 ⊢ A  ∼ B  ∶ U)
      →      𝔾 ⊢ t₁ ∼ t₂ ∶ B
