module Mono.Untyped.Substitution.Properties where
open import Mono.Prelude
open import Mono.Untyped.PreTerm
open import Mono.Untyped.Weakening
open import Mono.Untyped.Weakening.Properties
open import Mono.Untyped.Substitution

◑◑-assoc : ∀ {𝔩 𝔪 𝔫 𝔬} (ρ₁ : Sub 𝔫 𝔬) (𝓌₂ : Ren 𝔪 𝔫) (𝓌₃ : Ren 𝔩 𝔪)
  → (ρ₁ ◑ 𝓌₂) ◑ 𝓌₃ ≡ ρ₁ ◑ (𝓌₂ ∙ 𝓌₃)
◑◑-assoc ·        𝓌₂ 𝓌₃ = refl
◑◑-assoc (ρ₁ , t) 𝓌₂ 𝓌₃ = _,_ ⟨$⟩ ◑◑-assoc ρ₁ 𝓌₂ 𝓌₃ ⟨*⟩ sym (ren⊢‿∙ 𝓌₂ 𝓌₃ t)

◐◑-assoc : ∀ {𝔩 𝔪 𝔫 𝔬} (𝓌₁ : Ren 𝔫 𝔬) (ρ₂ : Sub 𝔪 𝔫) (𝓌₃ : Ren 𝔩 𝔪)
  → (𝓌₁ ◐ ρ₂) ◑ 𝓌₃ ≡ 𝓌₁ ◐ (ρ₂ ◑ 𝓌₃)
◐◑-assoc  done     ·        𝓌₃ = refl
◐◑-assoc (skip 𝓌₁) (ρ₂ , t) 𝓌₃ = ◐◑-assoc 𝓌₁ ρ₂ 𝓌₃
◐◑-assoc (keep 𝓌₁) (ρ₂ , t) 𝓌₃ = _, _ ⟨$⟩ ◐◑-assoc 𝓌₁ ρ₂ 𝓌₃

◐-unitˡ : ∀ {𝔪 𝔫} (ρ : Sub 𝔪 𝔫) → id ◐ ρ ≡ ρ
◐-unitˡ ·       = refl
◐-unitˡ (ρ , t) = _, _ ⟨$⟩ ◐-unitˡ ρ

◑-unitˡ : ∀ {𝔪 𝔫} (𝓌 : Ren 𝔪 𝔫) → id ◑ 𝓌 ≡ ⌜ 𝓌 ⌝
◑-unitˡ  done    = refl
◑-unitˡ (skip 𝓌) = begin
  id ◑ skip 𝓌         ↑⟨ (id ◑_) ∘ skip ⟨$⟩ ∙-unitʳ 𝓌 ⟩
  id ◑ skip (𝓌 ∙ id)  ↓⟨ refl ⟩
  id ◑ (𝓌 ∙ ↑)        ↑⟨ ◑◑-assoc id 𝓌 ↑ ⟩
  (id ◑ 𝓌) ◑ ↑        ↓⟨ _◑ _ ⟨$⟩ ◑-unitˡ 𝓌 ⟩
  ⌜ 𝓌 ⌝ ◑ ↑           ∎
◑-unitˡ (keep 𝓌) = _, _ ⟨$⟩ (begin
  (id ◑ ↑) ◑ keep 𝓌   ↓⟨ ◑◑-assoc id ↑ (keep 𝓌) ⟩
  id ◑ (↑ ∙ keep 𝓌)   ↓⟨ refl ⟩
  id ◑ skip (id ∙ 𝓌)  ↓⟨ (id ◑_) ∘ skip ⟨$⟩ ∙-unitˡ 𝓌 ⟩
  id ◑ skip 𝓌         ↓⟨ ◑-unitˡ (skip 𝓌) ⟩
  ⌜ 𝓌 ⌝ ◑ ↑           ∎)

◐-unitʳ : ∀ {𝔪 𝔫} (𝓌 : Ren 𝔪 𝔫) → 𝓌 ◐ id ≡ ⌜ 𝓌 ⌝
◐-unitʳ  done    = refl
◐-unitʳ (skip 𝓌) = begin
  𝓌 ◐ (id ◑ ↑)  ↑⟨ ◐◑-assoc 𝓌 id ↑ ⟩
  (𝓌 ◐ id) ◑ ↑  ↓⟨ _◑ ↑ ⟨$⟩ ◐-unitʳ 𝓌 ⟩
  ⌜ 𝓌 ⌝ ◑ ↑     ∎
◐-unitʳ (keep 𝓌) = _, _ ⟨$⟩ ◐-unitʳ (skip 𝓌)

sub∋-◐ : ∀ {𝔩 𝔪 𝔫} (𝓌 : Ren 𝔪 𝔫) (ρ : Sub 𝔩 𝔪) (x : Var 𝔫)
  → sub∋ (𝓌 ◐ ρ) x ≡ sub∋ ρ (ren∋ 𝓌 x)
sub∋-◐  done    ·       ()
sub∋-◐ (skip 𝓌) (ρ , t) x       = sub∋-◐ 𝓌 ρ x
sub∋-◐ (keep 𝓌) (ρ , t) zero    = refl
sub∋-◐ (keep 𝓌) (ρ , t) (suc x) = sub∋-◐ 𝓌 ρ x

⌜keep⌝◐ : ∀ {𝔩 𝔪 𝔫} (𝓌 : Ren 𝔪 𝔫) (ρ : Sub 𝔩 𝔪)
  → ⌜keep⌝ (𝓌 ◐ ρ) ≡ keep 𝓌 ◐ ⌜keep⌝ ρ
⌜keep⌝◐ 𝓌 ρ = _, _ ⟨$⟩ ◐◑-assoc 𝓌 ρ ↑

sub⊢‿⌜keep⌝◐ : ∀ {𝔩 𝔪 𝔫} (𝓌 : Ren 𝔪 𝔫) (ρ : Sub 𝔩 𝔪) (t : Tm (suc 𝔫))
  → sub⊢ (⌜keep⌝ (𝓌 ◐ ρ)) t ≡ sub⊢ (keep 𝓌 ◐ ⌜keep⌝ ρ) t
sub⊢‿⌜keep⌝◐ 𝓌 ρ t = (λ ρ → sub⊢ ρ t) ⟨$⟩ ⌜keep⌝◐ 𝓌 ρ

sub⊢‿◐ : ∀ {𝔩 𝔪 𝔫} (𝓌 : Ren 𝔪 𝔫) (ρ : Sub 𝔩 𝔪) (t : Tm 𝔫)
  → sub⊢ (𝓌 ◐ ρ) t ≡ sub⊢ ρ (ren⊢ 𝓌 t)
sub⊢‿◐ 𝓌 ρ (U)       = refl
sub⊢‿◐ 𝓌 ρ (Pi A B)  = Pi ⟨$⟩ sub⊢‿◐ 𝓌 ρ A
                          ⟨*⟩ (sub⊢‿⌜keep⌝◐ 𝓌 ρ B ⋮ sub⊢‿◐ (keep 𝓌) (⌜keep⌝ ρ) B)
sub⊢‿◐ 𝓌 ρ (T)       = refl
sub⊢‿◐ 𝓌 ρ (var x)   = sub∋-◐ 𝓌 ρ x
sub⊢‿◐ 𝓌 ρ (lam t)   = lam ⟨$⟩ (sub⊢‿⌜keep⌝◐ 𝓌 ρ t ⋮ sub⊢‿◐ (keep 𝓌) (⌜keep⌝ ρ) t )
sub⊢‿◐ 𝓌 ρ (app t u) = app ⟨$⟩ sub⊢‿◐ 𝓌 ρ t ⟨*⟩ sub⊢‿◐ 𝓌 ρ u
sub⊢‿◐ 𝓌 ρ (tt)      = refl

sub∋-◑ : ∀ {𝔩 𝔪 𝔫} (ρ : Sub 𝔪 𝔫) (𝓌 : Ren 𝔩 𝔪) (x : Var 𝔫)
  → sub∋ (ρ ◑ 𝓌) x ≡ ren⊢ 𝓌 (sub∋ ρ x)
sub∋-◑ ·       𝓌 ()
sub∋-◑ (ρ , t) 𝓌 zero    = refl
sub∋-◑ (ρ , t) 𝓌 (suc x) = sub∋-◑ ρ 𝓌 x

⌜keep⌝◑ : ∀ {𝔩 𝔪 𝔫} (ρ : Sub 𝔪 𝔫) (𝓌 : Ren 𝔩 𝔪)
  → ⌜keep⌝ (ρ ◑ 𝓌) ≡ ⌜keep⌝ ρ ◑ keep 𝓌
⌜keep⌝◑ ρ 𝓌 = _, _ ⟨$⟩ (begin
  (ρ ◑ 𝓌) ◑ ↑         ↓⟨ ◑◑-assoc ρ 𝓌 ↑ ⟩
  ρ ◑ (𝓌 ∙ ↑)         ↓⟨ (ρ ◑_) ∘ skip ⟨$⟩ (∙-unitʳ 𝓌 ⋮ sym (∙-unitˡ 𝓌)) ⟩
  ρ ◑ (↑ ∙ keep 𝓌)    ↑⟨ ◑◑-assoc ρ ↑ (keep 𝓌) ⟩
  (ρ ◑ ↑) ◑ (keep 𝓌)  ∎)

sub⊢‿⌜keep⌝◑ : ∀ {𝔩 𝔪 𝔫} (ρ : Sub 𝔪 𝔫) (𝓌 : Ren 𝔩 𝔪) (t : Tm (suc 𝔫))
  → sub⊢ (⌜keep⌝ (ρ ◑ 𝓌)) t ≡ sub⊢ (⌜keep⌝ ρ ◑ keep 𝓌) t
sub⊢‿⌜keep⌝◑ ρ 𝓌 t = (λ ρ → sub⊢ ρ t) ⟨$⟩ ⌜keep⌝◑ ρ 𝓌

sub⊢‿◑ : ∀ {𝔩 𝔪 𝔫} (ρ : Sub 𝔪 𝔫) (𝓌 : Ren 𝔩 𝔪) (t : Tm 𝔫)
  → sub⊢ (ρ ◑ 𝓌) t ≡ ren⊢ 𝓌 (sub⊢ ρ t)
sub⊢‿◑ ρ 𝓌 (U)       = refl
sub⊢‿◑ ρ 𝓌 (Pi A B)  = Pi ⟨$⟩ sub⊢‿◑ ρ 𝓌 A
                          ⟨*⟩ (sub⊢‿⌜keep⌝◑ ρ 𝓌 B ⋮ sub⊢‿◑ (⌜keep⌝ ρ) (keep 𝓌) B)
sub⊢‿◑ ρ 𝓌 (T)       = refl
sub⊢‿◑ ρ 𝓌 (var x)   = sub∋-◑ ρ 𝓌 x
sub⊢‿◑ ρ 𝓌 (lam t)   = lam ⟨$⟩ (sub⊢‿⌜keep⌝◑ ρ 𝓌 t ⋮ sub⊢‿◑ (⌜keep⌝ ρ) (keep 𝓌) t)
sub⊢‿◑ ρ 𝓌 (app t u) = app ⟨$⟩ sub⊢‿◑ ρ 𝓌 t ⟨*⟩ sub⊢‿◑ ρ 𝓌 u
sub⊢‿◑ ρ 𝓌 (tt)      = refl

◑∘-assoc : ∀ {𝔩 𝔪 𝔫 𝔬} (ρ₁ : Sub 𝔫 𝔬) (𝓌₂ : Ren 𝔪 𝔫) (ρ₃ :  Sub 𝔩 𝔪)
  → (ρ₁ ◑ 𝓌₂) ∘ ρ₃ ≡ ρ₁ ∘ (𝓌₂ ◐ ρ₃)
◑∘-assoc ·        𝓌₂ ρ₃ = refl
◑∘-assoc (ρ₁ , t) 𝓌₂ ρ₃ = _,_ ⟨$⟩ ◑∘-assoc ρ₁ 𝓌₂ ρ₃ ⟨*⟩ sym (sub⊢‿◐ 𝓌₂ ρ₃ t)

∘◑-assoc : ∀ {𝔩 𝔪 𝔫 𝔬} (ρ₁ : Sub 𝔫 𝔬) (ρ₂ : Sub 𝔪 𝔫) (𝓌₃ : Ren 𝔩 𝔪)
  → (ρ₁ ∘ ρ₂) ◑ 𝓌₃ ≡ ρ₁ ∘ (ρ₂ ◑ 𝓌₃)
∘◑-assoc ·        ρ₂ 𝓌₃ = refl
∘◑-assoc (ρ₁ , t) ρ₂ 𝓌₃ = _,_ ⟨$⟩ ∘◑-assoc ρ₁ ρ₂ 𝓌₃ ⟨*⟩ sym (sub⊢‿◑ ρ₂ 𝓌₃ t)

sub∋-id : ∀ {𝔫} (x : Var 𝔫) → sub∋ id x ≡ var x
sub∋-id zero    = refl
sub∋-id (suc x) = begin
  sub∋ (id ◑ ↑) x     ↓⟨ sub∋-◑ id ↑ x ⟩
  ren⊢ ↑ (sub∋ id x)  ↓⟨ ren⊢ ↑ ⟨$⟩ sub∋-id x ⟩
  ren⊢ ↑ (var x)      ↓⟨ var ∘ suc ⟨$⟩ ren∋-id x ⟩
  var (suc x)         ∎

sub⊢‿id : ∀ {𝔫} (t : Tm 𝔫) → sub⊢ id t ≡ t
sub⊢‿id (U)       = refl
sub⊢‿id (Pi A B)  = Pi ⟨$⟩ sub⊢‿id A ⟨*⟩ sub⊢‿id B
sub⊢‿id (T)       = refl
sub⊢‿id (var x)   = sub∋-id x
sub⊢‿id (lam t)   = lam ⟨$⟩ sub⊢‿id t
sub⊢‿id (app t u) = app ⟨$⟩ sub⊢‿id t ⟨*⟩ sub⊢‿id u
sub⊢‿id (tt)      = refl

sub∋-∘ : ∀ {𝔩 𝔪 𝔫} (ρ₁ : Sub 𝔪 𝔫) (ρ₂ : Sub 𝔩 𝔪) (x : Var 𝔫)
  → sub∋ (ρ₁ ∘ ρ₂) x ≡ sub⊢ ρ₂ (sub∋ ρ₁ x)
sub∋-∘ ·        ρ₂ ()
sub∋-∘ (ρ₁ , t) ρ₂ zero    = refl
sub∋-∘ (ρ₁ , t) ρ₂ (suc x) = sub∋-∘ ρ₁ ρ₂ x

⌜keep⌝∘ : ∀ {𝔩 𝔪 𝔫} (ρ₁ : Sub 𝔪 𝔫) (ρ₂ : Sub 𝔩 𝔪)
  → ⌜keep⌝ (ρ₁ ∘ ρ₂) ≡ ⌜keep⌝ ρ₁ ∘ ⌜keep⌝ ρ₂
⌜keep⌝∘ ρ₁ ρ₂ = _, _ ⟨$⟩ (begin
  (ρ₁ ∘ ρ₂) ◑ ↑                   ↓⟨ ∘◑-assoc ρ₁ ρ₂ ↑ ⟩
  ρ₁ ∘ (ρ₂ ◑ ↑)                   ↑⟨ ρ₁ ∘_ ⟨$⟩ ◐-unitˡ (ρ₂ ◑ ↑) ⟩
  ρ₁ ∘ (id ◐ (ρ₂ ◑ ↑))            ↓⟨ refl ⟩
  ρ₁ ∘ (↑ ◐ (ρ₂ ◑ ↑ , var zero))  ↑⟨ ◑∘-assoc ρ₁ ↑ _ ⟩
  (ρ₁ ◑ ↑) ∘ (ρ₂ ◑ ↑ , var zero)  ∎)

sub⊢‿⌜keep⌝∘ : ∀ {𝔩 𝔪 𝔫} (ρ₁ : Sub 𝔪 𝔫) (ρ₂ : Sub 𝔩 𝔪) (t : Tm (suc 𝔫))
  → sub⊢ (⌜keep⌝ (ρ₁ ∘ ρ₂)) t ≡ sub⊢ (⌜keep⌝ ρ₁ ∘ ⌜keep⌝ ρ₂) t
sub⊢‿⌜keep⌝∘ ρ₁ ρ₂ t = (λ ρ → sub⊢ ρ t) ⟨$⟩ ⌜keep⌝∘ ρ₁ ρ₂

sub⊢‿∘ : ∀ {𝔩 𝔪 𝔫} (ρ₁ : Sub 𝔪 𝔫) (ρ₂ : Sub 𝔩 𝔪) (t : Tm 𝔫)
  → sub⊢ (ρ₁ ∘ ρ₂) t ≡ sub⊢ ρ₂ (sub⊢ ρ₁ t)
sub⊢‿∘ ρ₁ ρ₂ (U)       = refl
sub⊢‿∘ ρ₁ ρ₂ (Pi A B)  = Pi ⟨$⟩ sub⊢‿∘ ρ₁ ρ₂ A
                            ⟨*⟩ (sub⊢‿⌜keep⌝∘ ρ₁ ρ₂ B ⋮ sub⊢‿∘ (⌜keep⌝ ρ₁) (⌜keep⌝ ρ₂) B)
sub⊢‿∘ ρ₁ ρ₂ (T)       = refl
sub⊢‿∘ ρ₁ ρ₂ (var x)   = sub∋-∘ ρ₁ ρ₂ x
sub⊢‿∘ ρ₁ ρ₂ (lam t)   = lam ⟨$⟩ (sub⊢‿⌜keep⌝∘ ρ₁ ρ₂ t ⋮ sub⊢‿∘ (⌜keep⌝ ρ₁) (⌜keep⌝ ρ₂) t)
sub⊢‿∘ ρ₁ ρ₂ (app t u) = app ⟨$⟩ sub⊢‿∘ ρ₁ ρ₂ t ⟨*⟩ sub⊢‿∘ ρ₁ ρ₂ u
sub⊢‿∘ ρ₁ ρ₂ (tt)      = refl

∘-unitˡ : ∀ {𝔪 𝔫} (ρ : Sub 𝔪 𝔫) → id ∘ ρ ≡ ρ
∘-unitˡ ·       = refl
∘-unitˡ (ρ , t) = _, _ ⟨$⟩ (begin
  (id ◑ ↑) ∘ (ρ , t)  ↓⟨ ◑∘-assoc id ↑ _ ⟩
  id ∘ (↑ ◐ (ρ , t))  ↓⟨ refl ⟩
  id ∘ (id ◐ ρ)       ↓⟨ id ∘_ ⟨$⟩ ◐-unitˡ ρ ⟩
  id ∘ ρ              ↓⟨ ∘-unitˡ ρ ⟩
  ρ                   ∎)

∘-unitʳ : ∀ {𝔪 𝔫} (ρ : Sub 𝔪 𝔫) → ρ ∘ id ≡ ρ
∘-unitʳ ·       = refl
∘-unitʳ (ρ , t) = _,_ ⟨$⟩ ∘-unitʳ ρ ⟨*⟩ sub⊢‿id t

∘-assoc : ∀ {𝔩 𝔪 𝔫 𝔬} (ρ₁ : Sub 𝔫 𝔬) (ρ₂ : Sub 𝔪 𝔫) (ρ₃ : Sub 𝔩 𝔪)
  → (ρ₁ ∘ ρ₂) ∘ ρ₃ ≡ ρ₁ ∘ (ρ₂ ∘ ρ₃)
∘-assoc ·        ρ₂ ρ₃ = refl
∘-assoc (ρ₁ , t) ρ₂ ρ₃ = _,_ ⟨$⟩ ∘-assoc ρ₁ ρ₂ ρ₃ ⟨*⟩ sym (sub⊢‿∘ ρ₂ ρ₃ t)

ren⊢‿sub₁ : ∀ {𝔪 𝔫} {𝓌 : Ren 𝔪 𝔫} (t : Tm (suc 𝔫)) {u : Tm 𝔫} → ren⊢ 𝓌 (t [ u ]₁) ≡ ren⊢ (keep 𝓌) t [ ren⊢ 𝓌 u ]₁
ren⊢‿sub₁ {𝓌 = 𝓌} t {u} = begin
  ren⊢ 𝓌 (sub⊢ (id , u) t)                ↑⟨ sub⊢‿◑ _ 𝓌 t ⟩
  sub⊢ ((id , u) ◑ 𝓌) t                   ↓⟨ refl ⟩
  sub⊢ (id ◑ 𝓌 , ren⊢ 𝓌 u) t              ↓⟨ (λ ρ → sub⊢ (ρ , ren⊢ 𝓌 u) t) ⟨$⟩ (◑-unitˡ 𝓌 ⋮ sym (◐-unitʳ 𝓌)) ⟩
  sub⊢ (𝓌 ◐ id , ren⊢ 𝓌 u) t              ↓⟨ refl ⟩
  sub⊢ (keep 𝓌 ◐ (id , ren⊢ 𝓌 u)) t       ↓⟨ sub⊢‿◐ (keep 𝓌) _ t ⟩
  sub⊢ (id , ren⊢ 𝓌 u) (ren⊢ (keep 𝓌) t)  ∎
