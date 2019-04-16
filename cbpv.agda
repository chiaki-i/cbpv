module cbpv where

open import Prelude.Bool renaming (Bool to 𝔹)

-- type
data typ : Set where
  B : typ
  _+_ : typ → typ → typ
  _⇒_ : typ → typ → typ

infixl 8 _+_
infixr 7 _⇒_

data term[_]_ (var : typ → Set) : typ → Set where
  Bool : 𝔹 → term[ var ] B
  Var  : {τ₁ : typ} → var τ₁ → term[ var ] τ₁
  Let  : {τ₁ τ₂ : typ} → term[ var ] τ₁ → term[ var ] τ₂
  If   : {τ₁ : typ} → term[ var ] B →
         term[ var ] τ₁ → term[ var ] τ₁ → term[ var ] τ₁
  Inl  : {τ₁ τ₂ : typ} → term[ var ] τ₁ → term[ var ] (τ₁ + τ₂)
  Inr  : {τ₁ τ₂ : typ} → term[ var ] τ₂ → term[ var ] (τ₁ + τ₂)
  Pm   : {τ₁ τ₂ τ₃ : typ} → term[ var ] (τ₁ + τ₂) →
         (var τ₁ → term[ var ] τ₃) →
         (var τ₂ → term[ var ] τ₃) → term[ var  ] τ₃
  Fun  : {τ₁ τ₂ : typ} → (var τ₂ → term[ var ] τ₁) →
         term[ var ] (τ₂ ⇒ τ₁)
  App  : {τ₁ τ₂ : typ} → term[ var ] (τ₂ ⇒ τ₁) →
         term[ var ] τ₂ → term[ var ] τ₁
