module CBV where

open import Agda.Builtin.Bool renaming (Bool to 𝔹)
open import Agda.Builtin.Char renaming (Char to ℂ)
open import Agda.Builtin.String renaming (String to 𝕊; primStringAppend to _^_)
open import Agda.Builtin.List
open import Function using (_∘_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

-- type
data typ : Set where
  B : typ
  _+_ : typ → typ → typ
  _⇒_ : typ → typ → typ

infixl 8 _+_
infixr 7 _⇒_

mutual
  data value[_]_ (var : typ → Set) : typ → Set where
    True  : value[ var ] B
    False : value[ var ] B
    Var   : {τ₁ : typ} → var τ₁ → value[ var ] τ₁
    Inl   : {τ₁ τ₂ : typ} → value[ var ] τ₁ → value[ var ] (τ₁ + τ₂)
    Inr   : {τ₁ τ₂ : typ} → value[ var ] τ₂ → value[ var ] (τ₁ + τ₂)
    Fun   : {τ₁ τ₂ : typ} → (var τ₂ → term[ var ] τ₁) →
           value[ var ] (τ₂ ⇒ τ₁)

  data term[_]_ (var : typ → Set) : typ → Set where
    Val   : {τ₁ : typ} → value[ var ] τ₁ → term[ var ] τ₁
    Let   : {τ₁ τ₂ : typ} → term[ var ] τ₁ →
            (var τ₁ → term[ var ] τ₂) → term[ var ] τ₂
    If    : {τ₁ : typ} → value[ var ] B →
            term[ var ] τ₁ → term[ var ] τ₁ → term[ var ] τ₁
    Pm    : {τ₁ τ₂ τ₃ : typ} → term[ var ] (τ₁ + τ₂) →
            (var τ₁ → term[ var ] τ₃) →
            (var τ₂ → term[ var ] τ₃) → term[ var ] τ₃
    App   : {τ₁ τ₂ : typ} → term[ var ] (τ₂ ⇒ τ₁) →
            term[ var ] τ₂ → term[ var ] τ₁
    Print : {τ₁ : typ} → 𝕊 → term[ var ] τ₁ → term[ var ] τ₁

-- 1.3.3 pg.7 η-law
mutual
  data SubstVal {var : typ → Set} : {τ₁ τ₂ : typ} →
                (var τ₁ → value[ var ] τ₂) →
                value[ var ] τ₁ → value[ var ] τ₂ → Set where
    sTrue  : {τ : typ} {v : value[ var ] τ} {b : var B} →
             SubstVal (λ _ → True) v True
    sFalse : {τ : typ} {v : value[ var ] τ} {b : var B} →
             SubstVal (λ _ → False) v False
    sVar=  : {τ : typ} {v : value[ var ] τ} →
             SubstVal (λ x → Var x) v v
    sVar≠  : {τ τ₁ : typ} {v : value[ var ] τ} {x : var τ₁} →
             SubstVal (λ _ → Var x) v (Var x)
    sInl   : {τ τ₁ τ₂  : typ} →
             {v₁ : var τ → value[ var ] τ₁} →
             {v : value[ var ] τ} →
             {v₁′ : value[ var ] τ₁} →
             SubstVal (λ x → v₁ x) v v₁′ →
             SubstVal (λ x → Inl {τ₂ = τ₂} (v₁ x)) v (Inl v₁′)
    sInr   : {τ τ₁ τ₂  : typ} →
             {v₁ : var τ → value[ var ] τ₂} →
             {v : value[ var ] τ} →
             {v₁′ : value[ var ] τ₂} →
             SubstVal (λ x → v₁ x) v v₁′ →
             SubstVal (λ x → Inr {τ₁ = τ₁} (v₁ x)) v (Inr v₁′)
    sFun   : {τ τ₁ τ₂ : typ}
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
           {e₁ : var τ → var τ₁ → term[ var ] τ₃} →
           {e₁′ : var τ₁ → term[ var ] τ₃} →
           {e₂ : var τ → var τ₂ → term[ var ] τ₃} →
           {e₂′ : var τ₂ → term[ var ] τ₃} →
           SubstVal (λ y → v₀ y) v v₀′ →
           ((x : var τ₁) → Subst (λ y → e₁ y x) v (e₁′ x)) →
           ((x : var τ₂) → Subst (λ y → e₂ y x) v (e₂′ x)) →
           Subst (λ y → Pm (Val (v₀ y)) (e₁ y) (e₂ y)) v (Pm (Val v₀′) e₁′ e₂′)
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

env : Set
env = List typ

⟦_⟧ᵗ : typ → Set
⟦ B ⟧ᵗ = 𝔹
⟦ τ₁ + τ₂ ⟧ᵗ = ⟦ τ₁ ⟧ᵗ ⊎ ⟦ τ₂ ⟧ᵗ
⟦ τ₁ ⇒ τ₂ ⟧ᵗ = ⟦ τ₁ ⟧ᵗ → (𝕊 × ⟦ τ₂ ⟧ᵗ)

mutual
  ⟦_⟧ᵛ : {var : Set → Set} {τ₁ : typ} →
         (v₁ : value[ var ∘ ⟦_⟧ᵗ ] τ₁) → (ρ : env) → ⟦ τ₁ ⟧ᵗ
  ⟦ True ⟧ᵛ ρ = true
  ⟦ False ⟧ᵛ ρ = false
  ⟦ Var x ⟧ᵛ ρ = {!!}
  ⟦_⟧ᵛ {var} (Inl v) ρ = inj₁ (proj₂ (⟦_⟧ʳ {var} (Val v) ρ))
  ⟦_⟧ᵛ {var} (Inr v) ρ = inj₂ (proj₂ (⟦_⟧ʳ {var} (Val v) ρ))
  ⟦ Fun M ⟧ᵛ ρ = λ x → {!!}

  ⟦_⟧ʳ : {var : Set → Set} {τ₁ : typ} →
         (e₁ : term[ var ∘ ⟦_⟧ᵗ ] τ₁) → (ρ : env) → (𝕊 × ⟦ τ₁ ⟧ᵗ)
  ⟦ Val v ⟧ʳ ρ = {!"" , (⟦ v ⟧ᵛ ρ)!}
  ⟦ Let e₁ x ⟧ʳ ρ = {!!}
  ⟦ If True e₁ e₂ ⟧ʳ ρ = {!!}
  ⟦ If False e₁ e₂ ⟧ʳ ρ = {!!}
  ⟦ If (Var x) e₁ e₂ ⟧ʳ ρ = {!!}
  ⟦ Pm e₁ x x₁ ⟧ʳ ρ = {!!}
  ⟦ App e₁ e₂ ⟧ʳ ρ = {!!}
  ⟦ Print x e₁ ⟧ʳ ρ = {!!}

data _⇓ᵛ_,_ {var : typ → Set} : {τ₁ : typ} →
     (M : term[ var ] τ₁) → (m : 𝕊) → (V : value[ var ] τ₁) → Set where
  ᵛTrue  : (b : var B) → Val (Var b) ⇓ᵛ "" , True
  ᵛFalse : (b : var B) → Val (Var b) ⇓ᵛ "" , False
  ᵛIfT   : {τ₁ : typ} →
           {M : value[ var ] B} {N N′ : term[ var ] τ₁} → 
           {m : 𝕊} {m′ : 𝕊} {V : value[ var ] τ₁} →
           Val M ⇓ᵛ m , True → N ⇓ᵛ m′ , V →
           If M N N′ ⇓ᵛ (m ^ m′) , V
  ᵛIfF   : {τ₁ : typ} →
           {M : value[ var ] B} {N N′ : term[ var ] τ₁} →
           {m : 𝕊} {m′ : 𝕊} {V : value[ var ] τ₁} →
           Val M ⇓ᵛ m , False → N′ ⇓ᵛ m′ , V →
           If M N N′ ⇓ᵛ (m ^ m′) , V
  ᵛInl   : {τ₁ τ₂ : typ} →
           {V : value[ var ] τ₁} {m : 𝕊} {V′ : value[ var ] τ₁} →
           Val V ⇓ᵛ m , V′ →
           Val (Inl {τ₂ = τ₂} V) ⇓ᵛ m , Inl V′
  ᵛInr   : {τ₁ τ₂ : typ} →
           {V : value[ var ] τ₂} {m : 𝕊} {V′ : value[ var ] τ₂} →
           Val V ⇓ᵛ m , V′ →
           Val (Inr {τ₁ = τ₁} V) ⇓ᵛ m , Inr V′
  ᵛPml   : {τ₁ τ₂ τ₃ : typ} →
           {M : term[ var ] (τ₁ + τ₂)} →
           {N₀ : var τ₁ → term[ var ] τ₃} →
           {N : term[ var ] τ₃} {N′ : term[ var ] τ₃} →
           {V : value[ var ] τ₁} {W : value[ var ] τ₃} →
           {m m′ : 𝕊} →
           (sub : Subst (λ x → N₀ x) V N) →
           M ⇓ᵛ m , Inl V → N ⇓ᵛ m′ , W →
           Pm M (λ x → N) (λ x → N′) ⇓ᵛ (m ^ m′) , W
  ᵛPmr   : {τ₁ τ₂ τ₃ : typ} →
           {M : term[ var ] (τ₁ + τ₂)} →
           {N′ : var τ₂ → term[ var ] τ₃} →
           {N : term[ var ] τ₃} {N″ : term[ var ] τ₃} →
           {V : value[ var ] τ₂} {W : value[ var ] τ₃} →
           {m m′ : 𝕊} →
           (sub : Subst (λ x → N′ x) V N″) →
           M ⇓ᵛ m , Inr V → N″ ⇓ᵛ m′ , W →
           Pm M (λ x → N) (λ x → N″) ⇓ᵛ (m ^ m′) , W
  ᵛFun   : {τ τ₁ : typ} →
           {M : var τ → term[ var ] τ₁} →
           Val (Fun (λ x → M x)) ⇓ᵛ "" , Fun (λ x → M x)
  ᵛApp   : {τ₁ τ₂ : typ} →
           {V : value[ var ] τ₂} {W : value[ var ] τ₁} →
           {M : term[ var ] τ₂} {N : term[ var ] (τ₂ ⇒ τ₁)} →
           {N′ : var τ₂ → term[ var ] τ₁} {N″ : term[ var ] τ₁} →
           {m m′ m″ : 𝕊} →
           Subst (λ x → N′ x) V N″ →
           M ⇓ᵛ m , V → N ⇓ᵛ m′ , Fun (λ x → N″) → N″ ⇓ᵛ m″ , W →
           App N M ⇓ᵛ m ^ (m′ ^ m″) , W
  ᵛPrint : {τ₁ : typ} →
           {V : value[ var ] τ₁} →
           {M : term[ var ] τ₁} →
           {m c : 𝕊} →
           M ⇓ᵛ m , V →
           Print c M ⇓ᵛ c ^ m , V
