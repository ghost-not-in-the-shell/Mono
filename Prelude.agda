module Mono.Prelude where
open import Agda.Primitive
open import Agda.Builtin.Equality public
open import Agda.Builtin.Nat      public

infixl 4 _⟨$⟩_
infixl 4 _⟨*⟩_

sym : ∀ {𝔞} {A : Set 𝔞} {x y : A}
  → x ≡ y
  → y ≡ x
sym refl = refl

_⋮_ : ∀ {𝔞} {A : Set 𝔞} {x y z : A}
  → x ≡ y
  → y ≡ z
  → x ≡ z
refl ⋮ refl = refl

_⟨$⟩_ : ∀ {𝔞 𝔟} {A : Set 𝔞} {B : Set 𝔟} (f : A → B) {x₁ x₂}
  →   x₁ ≡   x₂
  → f x₁ ≡ f x₂
f ⟨$⟩ refl = refl

_⟨*⟩_ : ∀ {𝔞 𝔟} {A : Set 𝔞} {B : Set 𝔟} {f₁ f₂ : A → B} {x₁ x₂}
  → f₁    ≡    f₂
  → x₁    ≡    x₂
  → f₁ x₁ ≡ f₂ x₂
refl ⟨*⟩ refl = refl

_⟦_⟫ : ∀ {𝔞} {A₁ A₂ : Set 𝔞}
  → A₁
  → A₁ ≡ A₂
  → A₂
x ⟦ refl ⟫ = x

module ≡-Reasoning where
  infix  1 begin_
  infixr 2 _↓⟨_⟩_
  infixr 2 _↑⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {𝔞} {A : Set 𝔞} {x y : A}
    → x ≡ y
    → x ≡ y
  begin x≡y = x≡y

  _↓⟨_⟩_ : ∀ {𝔞} {A : Set 𝔞} (x {y z} : A)
    → x ≡ y
    → y ≡ z
    → x ≡ z
  x ↓⟨ x≡y ⟩ y≡z = x≡y ⋮ y≡z

  _↑⟨_⟩_ : ∀ {𝔞} {A : Set 𝔞} (x {y z} : A)
    → y ≡ x
    → y ≡ z
    → x ≡ z
  x ↑⟨ y≡x ⟩ y≡z = sym y≡x ⋮ y≡z

  _∎ : ∀ {𝔞} {A : Set 𝔞}
    → (x : A)
    → x ≡ x
  x ∎ = refl

open ≡-Reasoning public

record Category {𝔠₀ 𝔠₁} {𝓒₀ : Set 𝔠₀} (Hom : 𝓒₀ → 𝓒₀ → Set 𝔠₁) : Set (𝔠₀ ⊔ 𝔠₁) where
  infixr 6 _∘_
  field
    id  : ∀ {A} → Hom A A
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C

open Category ⦃...⦄ public

{-# DISPLAY Category.id  _ = id  #-}
{-# DISPLAY Category._∘_ _ = _∘_ #-}

instance
  𝒮ℯ𝓉 : ∀ {𝔞} → Category λ (A B : Set 𝔞) → A → B
  id  ⦃ 𝒮ℯ𝓉 ⦄ = λ x → x
  _∘_ ⦃ 𝒮ℯ𝓉 ⦄ = λ g f x → g (f x)
