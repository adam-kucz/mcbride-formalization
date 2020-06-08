{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Basic using (Rig; wfs)

module Syntax.Context.Arbitrary
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Syntax

open import Type.Sum hiding (_,_)
open import Data.Nat hiding (_⊔_)
open import Data.Maybe
open import Data.Tree.Binary

HoleType = Maybe (ExprTag × ℕ)
Holes = BinaryTree HoleType

pattern ◻ = leaf nothing
pattern [_] x = leaf (just x)

data Context
  : --------------------------------------------------------------------------
  (holes : Holes) -- required (type, number of free variables) of holes
  (result : ExprTag) -- type resulting from filling all holes
  (n : ℕ) -- number of free variables of the context (∀ m ∈ ms → n ≤ m)
  → 𝒰 ⁺ ⊔ 𝒱 ˙
  where
  term : (t : Term n)
    → -------------------
    Context ◻ term n

  elim : (e : Elim n)
    → -------------------
    Context ◻ elim n

  — : ∀ {tag n}
    → ------------------
    Context [ tag Σ., n ] tag n

  [_x:_]→_ : ∀ {n l r}
    (π : R)
    (C₀ : Context l term n)
    (C₁ : Context r term (n +1))
    → ---------------------
    Context (l /\ r) term n

  λx,_ : ∀ {n t}
    (C : Context t term (n +1))
    → ----------------------
    Context t term n

  ⌊_⌋ : ∀ {n t}
    (C : Context t elim n)
    → ---------------------
    Context t term n

  _`_ : ∀ {n l r}
    (C₀ : Context l elim n)
    (C₁ : Context r term n)
    → ----------------------
    Context (l /\ r) elim n

  _꞉_ : ∀ {n l r}
    (C₀ : Context l term n)
    (C₁ : Context r term n)
    →  ----------------------
    Context (l /\ r) elim n

open import Type.Unit

to-type : HoleType → 𝒰 ⁺ ⊔ 𝒱 ˙
to-type nothing = Lift𝒰 𝟙
to-type (just (tag Σ., m)) = expr-of-type tag m

all-types : Holes → 𝒰 ⁺ ⊔ 𝒱 ˙
all-types (leaf x) = to-type x
all-types (l /\ r) = all-types l × all-types r

fill-holes : ∀
  {t : Holes}
  (es : all-types t)
  {tag n}
  (C : Context t tag n)
  → ----------------------
  expr-of-type tag n
fill-holes es (term t) = t
fill-holes es (elim e) = e
fill-holes es — = es
fill-holes (l Σ., r) ([ π x: C₀ ]→ C₁) =
  [ π x: fill-holes l C₀ ]→ fill-holes r C₁
fill-holes es (λx, C) = λx, fill-holes es C
fill-holes es ⌊ C ⌋ = ⌊ fill-holes es C ⌋
fill-holes (l Σ., r) (C₀ ` C₁) = fill-holes l C₀ ` fill-holes r C₁
fill-holes (l Σ., r) (C₀ ꞉ C₁) = fill-holes l C₀ ꞉ fill-holes r C₁

-- open import Proposition.Empty
-- import Data.List as L
-- open import Collection

open import Logic
open import Proof

join : (l r : Holes) → Holes
join ◻ r = r
join l@([ _ ]) ◻ = l
join l@([ _ ]) r@([ _ ]) = l /\ r
join l@([ _ ]) r@(_ /\ _) = l /\ r
join l@(_ /\ _) ◻ = l
join l@(_ /\ _) r@([ _ ]) = l /\ r
join l@(_ /\ _) r@(_ /\ _) = l /\ r

collect-trim : Holes → Holes
collect-trim ◻ = ◻
collect-trim [ x ] = [ x ]
collect-trim (l /\ r) = join (collect-trim l)(collect-trim r)

{-
HolesListable : Listable _ Holes (ExprTag × ℕ)
HolesListable = NestedListable (ExprTag × ℕ) HoleType Holes
private
  instance
    _ = HolesListable

open import Structure.Monoid hiding (e)

holes-to-list = to-list ⦃ HolesListable ⦄

holes-to-list-∙ : ∀ l r
  → ------------------------------------------------------------
  holes-to-list l ∙ holes-to-list r == holes-to-list (l /\ r)
holes-to-list-∙ l r =
  proof holes-to-list l ∙ holes-to-list r
    === mconcat (L.map f (to-list l) ∙ L.map f (to-list r))
      :by: sym $ mconcat-∪ (L.map f (to-list l)) (L.map f (to-list r))
    === holes-to-list (l /\ r)
      :by: ap mconcat $ sym $ L.map++ (to-list l) (to-list r) f
  qed
  where f = to-list {Col = HoleType}

private
  to-list/\==∅ : (l r : Holes)
    (p : holes-to-list (l /\ r) == L.[])
    → --------------------------------------------
    holes-to-list l == L.[] ∧ holes-to-list r == L.[]
to-list/\==∅ l r p with (
  proof holes-to-list l ∙ holes-to-list r
    === holes-to-list (l /\ r)            :by: holes-to-list-∙ l r
    === L.[]                              :by: p
  qed)
... | q with holes-to-list l | holes-to-list r
to-list/\==∅ l r p | q | L.[] | L.[] = Id.refl L.[] , Id.refl L.[]

as-expr : ∀{t tag m}
  (C : Context t tag m)
  (p : to-list t == L.[] {X = ExprTag × ℕ})
  → ------------------------
  expr-of-type tag m
as-expr (term t) p = t
as-expr (elim e) p = e
as-expr {l /\ r} ([ π x: C₀ ]→ C₁) p =
  [ π x: as-expr C₀ (∧left $ to-list/\==∅ l r p) ]→
         as-expr C₁ (∧right $ to-list/\==∅ l r p)
as-expr (λx, C) p = λx, as-expr C p
as-expr ⌊ C ⌋ p = ⌊ as-expr C p ⌋
as-expr {l /\ r} (C₀ ` C₁) p =
  as-expr C₀ (∧left $ to-list/\==∅ l r p) `
  as-expr C₁ (∧right $ to-list/\==∅ l r p)
as-expr {l /\ r} (C₀ ꞉ C₁) p =
  as-expr C₀ (∧left $ to-list/\==∅ l r p) ꞉
  as-expr C₁ (∧right $ to-list/\==∅ l r p)
-}

open import Proposition.Unit
open import Relation.Binary

all-related : (R : RelOnExpr 𝒵)(t : Holes) → BinRel 𝒵 (all-types t)
all-related R ◻ es es' = Lift𝒰ᵖ ⊤ 
all-related R [ x ] e₀ e₁ = R e₀ e₁
all-related R (l /\ r) (es₀-l Σ., es₀-r) (es₁-l Σ., es₁-r) =
  all-related R l es₀-l es₁-l ∧ all-related R r es₀-r es₁-r

Reflexive-all-related :
  {R : RelOnExpr 𝒵}
  ⦃ reflexive : ∀ {n}{tag} → Reflexive (R {n}{tag}) ⦄
  {t : Holes}
  → ---------------------------
  Reflexive (all-related R t)
Transitive-all-related :
  {R : RelOnExpr 𝒵}
  ⦃ transitive : ∀ {n}{tag} → Transitive (R {n}{tag}) ⦄
  {t : Holes}
  → ---------------------------
  Transitive (all-related R t)
Symmetric-all-related :
  {R : RelOnExpr 𝒵}
  ⦃ symmetric : ∀ {n}{tag} → Symmetric (R {n}{tag}) ⦄
  {t : Holes}
  → ---------------------------
  Symmetric (all-related R t)

refl ⦃ Reflexive-all-related {t = ◻} ⦄ _ = ↑prop ⋆ₚ
refl ⦃ Reflexive-all-related ⦃ r ⦄ {[ tag Σ., n ]} ⦄ = refl ⦃ r ⦄
refl ⦃ Reflexive-all-related {t = l /\ r} ⦄ (es₀ Σ., es₁) =
  refl ⦃ Reflexive-all-related {t = l} ⦄ es₀ ,
  refl ⦃ Reflexive-all-related {t = r} ⦄ es₁

trans ⦃ Transitive-all-related {t = ◻} ⦄ _ _ = ↑prop ⋆ₚ
trans ⦃ Transitive-all-related ⦃ t ⦄ {[ x ]} ⦄ = trans ⦃ t ⦄
trans ⦃ Transitive-all-related {t = l /\ r} ⦄ (p₀ , p₁) (q₀ , q₁) =
  trans ⦃ Transitive-all-related {t = l} ⦄ p₀ q₀ ,
  trans ⦃ Transitive-all-related {t = r} ⦄ p₁ q₁

sym ⦃ Symmetric-all-related {t = ◻} ⦄ _ = ↑prop ⋆ₚ
sym ⦃ Symmetric-all-related ⦃ s ⦄ {[ x ]} ⦄ = sym ⦃ s ⦄
sym ⦃ Symmetric-all-related {t = l /\ r} ⦄ (p₀ , p₁) =
  sym ⦃ Symmetric-all-related {t = l} ⦄ p₀ ,
  sym ⦃ Symmetric-all-related {t = r} ⦄ p₁

record ContextClosed (R : RelOnExpr 𝒵) : 𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒵 ᵖ where
  field
    ctx-closed : ∀
      {t tag n}
      (C : Context t tag n)
      {es es' : all-types t}
      (p : all-related R t es es')
      → -------------------------------------------------------------
      R (fill-holes es C) (fill-holes es' C)

open ContextClosed ⦃ … ⦄ public
