module cbpv where

open import Data.Bool renaming (Bool to 𝔹)
open import Data.Char renaming (Char to ℂ)
open import Data.String renaming (String to 𝕊)

-- type
data typ : Set where
  B : typ
  _+_ : typ → typ → typ
  _⇒_ : typ → typ → typ

infixl 8 _+_
infixr 7 _⇒_

mutual
  data value[_]_ (var : typ → Set) : typ → Set where
    Bool : 𝔹 → value[ var ] B
    Var  : {τ₁ : typ} → var τ₁ → value[ var ] τ₁
    Inl  : {τ₁ τ₂ : typ} → value[ var ] τ₁ → value[ var ] (τ₁ + τ₂)
    Inr  : {τ₁ τ₂ : typ} → value[ var ] τ₂ → value[ var ] (τ₁ + τ₂)
    Fun  : {τ₁ τ₂ : typ} → (var τ₂ → term[ var ] τ₁) →
           value[ var ] (τ₂ ⇒ τ₁)

  data term[_]_ (var : typ → Set) : typ → Set where
    Val   : {τ₁ : typ} → value[ var ] τ₁ → term[ var ] τ₁
    Let   : {τ₁ τ₂ : typ} → term[ var ] τ₁ →
            (var τ₁ → term[ var ] τ₂) → term[ var ] τ₂
    If    : {τ₁ : typ} → value[ var ] B →
            term[ var ] τ₁ → term[ var ] τ₁ → term[ var ] τ₁
    Pm    : {τ₁ τ₂ τ₃ : typ} → term[ var ] (τ₁ + τ₂) →
            (var τ₁ → value[ var ] τ₃) →
            (var τ₂ → value[ var ] τ₃) → term[ var ] τ₃
    App   : {τ₁ τ₂ : typ} → term[ var ] (τ₂ ⇒ τ₁) →
            term[ var ] τ₂ → term[ var ] τ₁
    Print : {τ₁ : typ} → 𝕊 → term[ var ] τ₁ → term[ var ] τ₁

-- 1.3.3 pg.7 η-law
mutual
  data SubstVal {var : typ → Set} : {τ₁ τ₂ : typ} →
                (var τ₁ → value[ var ] τ₂) →
                value[ var ] τ₁ → value[ var ] τ₂ → Set where
    sBool : {τ : typ} {v : value[ var ] τ} {b : 𝔹} →
            SubstVal (λ _ → Bool b) v (Bool b)
    sVar= : {τ : typ} {v : value[ var ] τ} →
            SubstVal (λ x → Var x) v v
    sVar≠ : {τ τ₁ : typ} {v : value[ var ] τ} {x : var τ₁} →
            SubstVal (λ _ → Var x) v (Var x)
    sInl  : {τ τ₁ τ₂  : typ} →
            {v₁ : var τ → value[ var ] τ₁} →
            {v : value[ var ] τ} →
            {v₁′ : value[ var ] τ₁} →
            SubstVal (λ x → v₁ x) v v₁′ →
            SubstVal (λ x → Inl {τ₂ = τ₂} (v₁ x)) v (Inl v₁′)
    sInr  : {τ τ₁ τ₂  : typ} →
            {v₁ : var τ → value[ var ] τ₂} →
            {v : value[ var ] τ} →
            {v₁′ : value[ var ] τ₂} →
            SubstVal (λ x → v₁ x) v v₁′ →
            SubstVal (λ x → Inr {τ₁ = τ₁} (v₁ x)) v (Inr v₁′)
    sFun  : {τ τ₁ τ₂ : typ}
            {e₁ : var τ → var τ₂ → term[ var ] τ₁} →
            {v : value[ var ] τ} →
            {e₁′ : var τ₂ → term[ var ] τ₁} →
            ((x : var τ₂) → Subst (λ y → (e₁ y) x) v (e₁′ x)) →
            SubstVal (λ y → Fun (e₁ y)) v (Fun e₁′)

  data Subst {var : typ → Set} : {τ₁ τ₂ : typ} →
             (var τ₁ → term[ var ] τ₂) →
             value[ var ] τ₁ → term[ var ] τ₂ → Set where
    sVal : {τ τ₁ : typ} →
           {v₁ : var τ → value[ var ] τ₁} →
           {v : value[ var ] τ} →
           {v₁′ : value[ var ] τ₁} →
           SubstVal v₁ v v₁′ →
           Subst (λ y → Val (v₁ y)) v (Val v₁′)
    sIf  : {τ τ₁ : typ} → {b : value[ var ] B} →
           {e₁ : var τ → term[ var ] τ₁} →
           {e₂ : var τ → term[ var ] τ₁} →
           {v : value[ var ] τ} →
           {e₁′ : term[ var ] τ₁} →
           {e₂′ : term[ var ] τ₁} →
           Subst e₁ v e₁′ → Subst e₂ v e₂′ →
           Subst (λ x → If b (e₁ x) (e₂ x)) v (If b e₁′ e₂′)
    sPm  : {τ τ₁ τ₂ τ₃ : typ} →
           {v : value[ var ] τ} →
           {v₀ : var τ → value[ var ] (τ₁ + τ₂)} →
           {v₀′ : value[ var ] (τ₁ + τ₂)} →
           {v₁ : var τ → var τ₁ → value[ var ] τ₃} →
           {v₁′ : var τ₁ → value[ var ] τ₃} →
           {v₂ : var τ → var τ₂ → value[ var ] τ₃} →
           {v₂′ : var τ₂ → value[ var ] τ₃} →
           SubstVal (λ y → v₀ y) v v₀′ →
           ((x : var τ₁) → SubstVal (λ y → v₁ y x) v (v₁′ x)) →
           ((x : var τ₂) → SubstVal (λ y → v₂ y x) v (v₂′ x)) →
           Subst (λ y → Pm (Val (v₀ y)) (v₁ y) (v₂ y)) v (Pm (Val v₀′) v₁′ v₂′)
    sApp : {τ τ₁ τ₂ : typ} →
           {e₁ : var τ → term[ var ] (τ₂ ⇒ τ₁)} →
           {e₂ : var τ → term[ var ] τ₂} →
           {v : value[ var ] τ} →
           {e₁′ : term[ var ] (τ₂ ⇒ τ₁)} →
           {e₂′ : term[ var ] τ₂} →
           Subst e₁ v e₁′ → Subst e₂ v e₂′ →
           Subst (λ y → App (e₁ y) (e₂ y)) v (App e₁′ e₂′)
    sLet : {τ τ₁ τ₂ : typ} →
           {e₁ : var τ → term[ var ] τ₁} →
           {e₂ : var τ → var τ₁ → term[ var ] τ₂} →
           {v : value[ var ] τ} →
           {e₁′ : term[ var ] τ₁} →
           {e₂′ : var τ₁ → term[ var ] τ₂} →
           ((x : var τ₁) → Subst (λ y → (e₂ y) x) v (e₂′ x)) →
           ((x : var τ₁) → Subst (λ y → e₁ y) v e₁′) →
           Subst (λ y → Let (e₁ y) (e₂ y)) v (Let e₁′ e₂′)
