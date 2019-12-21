{-# OPTIONS --exact-split --safe --prop #-}
module Foundation.Prop'.Function where

open import Foundation.PropUniverses

id : (x : 𝑋) → 𝑋
id x = x
  
𝑖𝑑 : (𝑋 : 𝒰 ᵖ) (x : 𝑋) → 𝑋
𝑖𝑑 𝑋 = id

type-of : {𝑋 : 𝒰 ᵖ} (x : 𝑋) → 𝒰 ᵖ
type-of {𝑋 = 𝑋} _ = 𝑋

infixr 16 _$_
_$_ : {𝐴 : (p : 𝑋) → 𝒱 ᵖ}
  (f : (p : 𝑋) → 𝐴 p)
  (p : 𝑋)
  → -----------------------
  𝐴 p
f $ x = f x

infixl 25 _∘_
_∘_ : {𝐴 : (p : 𝑋) → 𝒰 ᵖ} {𝐾 : (p : 𝑋) (q : 𝐴 p) → 𝒱 ᵖ}
  (f : {p : 𝑋} (q : 𝐴 p) → 𝐾 p q)
  (g : (p : 𝑋) → 𝐴 p)
  → ----------------------------
  (p : 𝑋) → 𝐾 p (g p)
(f ∘ g) x = f (g x)

-- open import Foundation.Type.Natural

-- $type : (switch : 𝟜) → 𝒰ω
-- $type ₀ = {𝒰 𝒱 : Universe} {X : 𝒰 ˙} {A : (x : X) → 𝒱 ˙}
--   (f : (x : X) → A x) (x : X) → A x
-- $type ₁ = {𝒰 𝒱 : Universe} {X : 𝒰 ˙} {A : (x : X) → 𝒱 ᵖ}
--   (f : (x : X) → A x) (x : X) → A x
-- $type ₂ = {𝒰 𝒱 : Universe} {X : 𝒰 ᵖ} {A : (x : X) → 𝒱 ˙}
--   (f : (x : X) → A x) (x : X) → A x
-- $type ₃ = {𝒰 𝒱 : Universe} {X : 𝒰 ᵖ} {A : (x : X) → 𝒱 ᵖ}
--   (f : (x : X) → A x) (x : X) → A x
-- $type ₄fin

-- -- unfortunately, Agda cannot infer value of switch by itself T_T
-- poly$ : (switch : 𝟜) → $type switch
-- poly$ ₀ f x = f x
-- poly$ ₁ f x = f x
-- poly$ ₂ f x = f x
-- poly$ ₃ f x = f x
-- poly$ ₄fin

-- ∘X-kind : (switch : 𝟠) → ∀ 𝒰 → (𝒰 ⁺) ˙
-- ∘X-kind ₀ = _˙
-- ∘X-kind ₂ = _˙
-- ∘X-kind ₄ = _˙
-- ∘X-kind ₆ = _˙
-- ∘X-kind ₁ = _ᵖ
-- ∘X-kind ₃ = _ᵖ
-- ∘X-kind ₅ = _ᵖ
-- ∘X-kind ₇ = _ᵖ
-- ∘X-kind ₈fin

-- ∘type : (switch : 𝟠) → 𝒰ω
-- ∘type ₀ = {𝒰 𝒱 𝒲 : Universe}
--   {X : 𝒰 ˙} {A : (p : X) → 𝒱 ˙} {K : (p : X) (q : A p) → 𝒲 ᵖ}
--   (f : {p : X} (q : A p) → K p q)
--   (g : (p : X) → A p)
--   → ----------------------------
--   (p : X) → K p (g p)
-- ∘type ₁ = {𝒰 𝒱 𝒲 : Universe}
--   {𝑋 : 𝒰 ᵖ} {𝐴 : (p : 𝑋) → 𝒱 ᵖ} {𝐾 : (p : 𝑋) (q : 𝐴 p) → 𝒲 ᵖ}
--   (f : {p : 𝑋} (q : 𝐴 p) → 𝐾 p q)
--   (g : (p : 𝑋) → 𝐴 p)
--   → ----------------------------
--   (p : 𝑋) → 𝐾 p (g p)
-- ∘type ₂ = {𝒰 𝒱 𝒲 : Universe}
--   {𝑋 : 𝒰 ᵖ} {𝐴 : (p : 𝑋) → 𝒱 ᵖ} {𝐾 : (p : 𝑋) (q : 𝐴 p) → 𝒲 ᵖ}
--   (f : {p : 𝑋} (q : 𝐴 p) → 𝐾 p q)
--   (g : (p : 𝑋) → 𝐴 p)
--   → ----------------------------
--   (p : 𝑋) → 𝐾 p (g p)
-- ∘type ₃ = {𝒰 𝒱 𝒲 : Universe}
--   {𝑋 : 𝒰 ᵖ} {𝐴 : (p : 𝑋) → 𝒱 ᵖ} {𝐾 : (p : 𝑋) (q : 𝐴 p) → 𝒲 ᵖ}
--   (f : {p : 𝑋} (q : 𝐴 p) → 𝐾 p q)
--   (g : (p : 𝑋) → 𝐴 p)
--   → ----------------------------
--   (p : 𝑋) → 𝐾 p (g p)
-- ∘type ₄ = {𝒰 𝒱 𝒲 : Universe}
--   {𝑋 : 𝒰 ᵖ} {𝐴 : (p : 𝑋) → 𝒱 ᵖ} {𝐾 : (p : 𝑋) (q : 𝐴 p) → 𝒲 ᵖ}
--   (f : {p : 𝑋} (q : 𝐴 p) → 𝐾 p q)
--   (g : (p : 𝑋) → 𝐴 p)
--   → ----------------------------
--   (p : 𝑋) → 𝐾 p (g p)
-- ∘type ₅ = {𝒰 𝒱 𝒲 : Universe}
--   {𝑋 : 𝒰 ᵖ} {𝐴 : (p : 𝑋) → 𝒱 ᵖ} {𝐾 : (p : 𝑋) (q : 𝐴 p) → 𝒲 ᵖ}
--   (f : {p : 𝑋} (q : 𝐴 p) → 𝐾 p q)
--   (g : (p : 𝑋) → 𝐴 p)
--   → ----------------------------
--   (p : 𝑋) → 𝐾 p (g p)
-- ∘type ₆ = {𝒰 𝒱 𝒲 : Universe}
--   {𝑋 : 𝒰 ᵖ} {𝐴 : (p : 𝑋) → 𝒱 ᵖ} {𝐾 : (p : 𝑋) (q : 𝐴 p) → 𝒲 ᵖ}
--   (f : {p : 𝑋} (q : 𝐴 p) → 𝐾 p q)
--   (g : (p : 𝑋) → 𝐴 p)
--   → ----------------------------
--   (p : 𝑋) → 𝐾 p (g p)
-- ∘type ₇ = {𝒰 𝒱 𝒲 : Universe}
--   {𝑋 : 𝒰 ᵖ} {𝐴 : (p : 𝑋) → 𝒱 ᵖ} {𝐾 : (p : 𝑋) (q : 𝐴 p) → 𝒲 ᵖ}
--   (f : {p : 𝑋} (q : 𝐴 p) → 𝐾 p q)
--   (g : (p : 𝑋) → 𝐴 p)
--   → ----------------------------
--   (p : 𝑋) → 𝐾 p (g p)
-- ∘type ₈fin

-- poly∘ : (switch : 𝟠) → ∘type switch
-- poly∘ ₀ f g x = f (g x)
-- poly∘ ₁ f g x = f (g x)
-- poly∘ ₂ f g x = f (g x)
-- poly∘ ₃ f g x = f (g x)
-- poly∘ ₄ f g x = f (g x)
-- poly∘ ₅ f g x = f (g x)
-- poly∘ ₆ f g x = f (g x)
-- poly∘ ₇ f g x = f (g x)
-- poly∘ ₈fin


