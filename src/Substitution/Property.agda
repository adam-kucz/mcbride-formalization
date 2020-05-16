{-# OPTIONS --exact-split --prop #-} -- TODO: add --safe
open import Basic using (Rig; wfs)
open import PropUniverses

module Substitution.Property
  {R : 𝒰 ˙} ⦃ rig : Rig R ⦄
  {S : 𝒱 ˙} ⦃ wfs : wfs 𝒲 𝒯 S ⦄
  where

open import Substitution.Definition

open import Proposition.Comparable
open import Data.Nat hiding (l)
open import Relation.Binary hiding (_~_)
open import Function hiding (_$_)
open import Logic
open import Proof

open import Syntax ⦃ rig ⦄ ⦃ wfs ⦄
open import Liftable
open import Renaming

lift-nth :
  (f : Elim m)
  (p : n < m +1)
  → -------------------------------------------------------------
  lift (nthSub n p f) ~ nthSub (n +1) (s<s p) (shift f)
lift-nth f p new = refl (var new)
lift-nth {n = n} f p (old v)
  with compare (index v) _<_ n ⦃ Comparable< ⦄
lift-nth f p (old v) | lt _ = Het.refl (var (old (contract v _)))
lift-nth f p (old v) | eq _ = Het.refl (shift f)
lift-nth f p (old new) | gt n<0 = ⊥-recursion _ $ ¬-<0 _ n<0
lift-nth f p (old (old v)) | gt _ = Het.refl (var (old v))

-- open import Type.Sum hiding (_,_)
-- open import Data.Nat.Proof

open import Proposition.Identity.Coercion

-- private
--   lbn-coer : Sub (k + m +1) (k + m) == Sub (k + (m +1)) (k + m)
--   lbn-p : ∀ {k m n}(p : n < m +1) → k + n < k + m +1

-- lbn-coer {k}{m} = ap (λ — → Sub — (k + m)) $ sym $ +-suc k m
-- lbn-p {k}{m}{n} p =
--   proof k + n
--     〉 _<_ 〉 k + (m +1) :by: ap (k +_) p
--     ===    k + m +1   :by: +-suc k m
--   qed
           
-- lift-by-nthSub : ∀{m n}
--   (k : ℕ)
--   (f : Elim m)
--   (p : n < m +1)
--   → --------------------------------------------------
--   lift-by k (nthSub n p f)
--   ~
--   coe lbn-coer (nthSub (k + n) (lbn-p p) (shift-by ⦃ r = RenameableElim ⦄ k f))
-- lift-by-nthSub {m}{n} zero f p v =
--   proof lift-by 0 (nthSub n p f) v
--     het== nthSub n p f v
--       :by: lift-by-0~id (nthSub n p f) v
--     het== nthSub n p (shift-by 0 f) v
--       :by: ap (λ — → nthSub n p — v ) $ (sym $ ==→~ rename-id) f
--     het== (coe (Id-refl _) (nthSub n p (shift-by 0 f))) v
--       :by: ap (λ — → — v) $ sym {R = Het._==_} $
--            coe-eval (Id-refl _) (nthSub n p (shift-by 0 f))
--   qed
-- lift-by-nthSub {m}{n}(k +1) f p new =
--   proof lift-by ⦃ r = _ ⦄ ⦃ r = LiftableElim ⦄ (k +1) (nthSub n p f) new
--     === default new
--       :by: Id-refl _
--     === nthSub (k + n +1) (lbn-p p) (shift-by (k +1) f) new
--       :by: Id-refl _
--     het== (coe (lbn-coer {k +1}) (nthSub (k + n +1) _ (shift-by (k +1) f))) new
--       :by: Het.ap3 (λ (i : ℕ)(σ : Sub i (k + m +1))(v : Var i) → σ v)
--              (subrel $ sym $ +-suc (k +2) m)
--              (isym $ coe-eval lbn-coer (nthSub (k + n +1) _ (shift-by (k +1) f)))
--              (new==new (sym $ +-suc (k +1) m))
--   qed
--   where new==new : ∀ {m n}
--           (p : m == n)
--           → ------------------------------
--           new {m} Het.== new {n}
--         new==new (Id-refl m) = Het.refl new
-- -- have: Sub (k + m +2) (k + m +1)
-- -- want: Sub (k + (m +1) +1) (k + m +1)
-- lift-by-nthSub (k +1) f p (old v) = {!!}

-- postulate
--   sub-sub :
--     (σ' : Sub n k)
--     (σ : Sub m n)
--     → ----------------------------------
--     sub {tag = tag} (σ' ⍟ σ) ~ sub σ' ∘ sub σ

open import Proposition.Identity hiding (refl)
open import Axiom.FunctionExtensionality

-- postulate
--   sub-new-shift :
--     (f : Elim m)
--     → ------------------------------
--     sub (newSub f) ∘ shift ~ 𝑖𝑑 (expr-of-type tag m)

{-
⍟-newSub : ∀ (σ : Sub m n) f
  → ---------------------------------------
  σ ⍟ newSub f ~ newSub (sub σ f) ⍟ lift σ
⍟-newSub σ f new = refl (sub σ f)
⍟-newSub σ f (old v) = isym $ sub-new-shift (sub σ f) (σ v)

sub-sub-new :
  (σ : Sub m n)
  (e : expr-of-type tag (m +1))
  (f : Elim m)
  → ------------------------------------------------------
  (sub (lift σ) e) [ sub σ f /new] == sub σ (e [ f /new])
sub-sub-new σ e f = subrel {_R_ = Het._==_} (
  proof sub (newSub (sub σ f)) (sub (lift σ) e)
    het== sub (newSub (sub σ f) ⍟ lift σ) e
      :by: (sym $ sub-sub (newSub (sub σ f)) (lift σ)) e
    het== sub (σ ⍟ newSub f) e
      :by: ap (λ — → sub — e) $ fun-ext $ sym $ ⍟-newSub σ f
    het== sub σ (sub (newSub f) e)
      :by: sub-sub σ (newSub f) e
  qed)
-}

-- lift-⍟ :
--   (σ' : Sub n k)
--   (σ : Sub m n)
--   → ----------------------------------
--   lift (σ' ⍟ σ) ~ lift σ' ⍟ lift σ
-- lift-⍟ σ' σ new = Id.refl (default new)
-- lift-⍟ σ' σ (old v) =
--   proof lift (σ' ⍟ σ) (old v)
--     === shift (sub σ' (σ v))
--       :by: Id.refl _
--     === sub (lift σ') (shift (σ v))
--       :by: {!!}
--     === (lift σ' ⍟ lift σ) (old v)
--       :by: Id.refl _
--   qed

-- open import Axiom.FunctionExtensionality

-- sub-sub {tag = term} σ' σ (⋆ i) = Id.refl (⋆ i)
-- sub-sub {tag = term} σ' σ ([ ρ x: S ]→ T) = {!!}
-- sub-sub {tag = term} σ' σ (λx, t) =
--   proof λx, sub (lift (σ' ⍟ σ)) t
--     === λx, sub (lift σ' ⍟ lift σ) t
--       :by: ap (λ — → λx, sub — t) $ fun-ext $ lift-⍟ σ' σ
--     === λx, sub (lift σ') (sub (lift σ) t)
--       :by: ap λx,_ $ sub-sub (lift σ') (lift σ) t
--   qed
-- sub-sub {tag = term} σ' σ ⌊ e ⌋ = {!!}
-- sub-sub {tag = elim} σ' σ (var v) = Id.refl (sub σ' (σ v))
-- sub-sub {tag = elim} σ' σ (f ` s) = {!!}
-- sub-sub {tag = elim} σ' σ (s ꞉ S) = {!!}
    
--     -- sub (newSub (sub σ' f)) (sub (lift σ') e) === sub σ' (sub (newSub f) e)

private
  rs-co : ∀ {tag k} m →
    expr-of-type tag (k + m +1) == expr-of-type tag (k + (m +1))
rs-co {tag}{k} m = sym {R = _==_} $ ap (expr-of-type tag) $ +-suc k m


rename-sub : ∀ {k l m n tag}
  (ρ : Ren m n)
  (σ : Sub l m)
  (e : expr-of-type tag (k + l))
  → --------------------------------------------------------------------------
  rename (lift-by k ρ) (sub (lift-by k σ) e)
  ==
  sub (lift-by k (rename ⦃ r = RenameableFun ⦄ ρ σ)) e
-- rename-sub {k = k}{m}{n}{term} ρ (⋆ i) f = {!!}
  -- proof rename (lift-by k ρ)
  --         (sub (lift-by k σ₀) (coe (rs-co m) (⋆ i)))
  --   === ⋆ i
  --     :by: ap (rename ⦃ r = RenameableExpr ⦄ (lift-by k ρ)) $
  --          aux (lift-by k σ₀)
  --              (coe (rs-co m) (⋆ i))
  --              (+-suc k m)
  --              (coe-eval (rs-co m) (⋆ i))
  --   === sub (lift-by k σ₁) (coe (rs-co n) (⋆ i))
  --     :by: sym {R = _==_} $
  --          aux (lift-by k σ₁)
  --              (coe (rs-co n) (⋆ i))
  --              (+-suc k n)
  --              (coe-eval (rs-co n) (⋆ i))
  -- qed
  -- where σ₀ = newSub f
  --       σ₁ = newSub (rename ρ f)
  --       aux : ∀ {m n k}
  --         (σ : Sub n k)
  --         (v : Term n)
  --         (p : n == m)
  --         (q : v Het.== ⋆ {n = m} i)
  --         → --------------------
  --         sub σ v == ⋆ i
  --       aux σ (⋆ i) (Id-refl m) (Het.refl (⋆ i)) = Id-refl (⋆ i)
-- rename-sub {tag = term} ρ ([ π x: S ]→ T) f = {!!}
-- rename-sub {k = k}{m}{n}{term} ρ (λx, e) f = {!!}
{-
  proof rename (lift-by k ρ) (sub (lift-by k σ₀) (coe (rs-co m) (λx, e)))
    === rename (lift-by k ρ) (sub (lift-by k σ₀) (λx, coe (rs-co m) e))
      :by: ap (rename ⦃ r = RenameableExpr ⦄ (lift-by k ρ) ∘
                 sub (lift-by k σ₀)) $
           sym {R = _==_} $ move-coe e (sym $ +-suc k m)
    === λx, rename (lift (lift-by k ρ))
              (sub (lift (lift-by k σ₀)) (coe (rs-co m) e))
      :by: Id-refl _
    === λx, rename (lift (lift-by k ρ))
              (sub (lift-by (k +1) σ₀) (coe (rs-co m) e))
      :by: ap (λ — → λx, rename (lift (lift-by k ρ))
                           (sub — (coe (rs-co m) e))) $
           subrel {_P_ = _==_} $ fun-ext $
           lift-lift-by~ k σ₀
    === λx, rename (lift-by (k +1) ρ)
              (sub (lift-by (k +1) σ₀) (coe (rs-co m) e))
      :by: ap (λ — → λx, rename —
                          (sub (lift-by (k +1) σ₀) (coe (rs-co m) e))) $
           subrel {_P_ = _==_} $ fun-ext $
           lift-lift-by~ k ρ
    === λx, sub (lift-by (k +1) σ₁) (coe (rs-co n) e₀)
      :by: ap λx,_ $ rename-sub ρ e f
    === λx, sub (lift-by (k +1) σ₁) (coe (rs-co n) e₁)
      :by: ap (λ — → λx, sub (lift-by (k +1) σ₁)
                       (coe (rs-co n) (rename — e))) $
           subrel {_P_ = _==_} $ fun-ext $ sym $
           lift-lift-by~ (k +1) ρ
    === λx, sub (lift (lift-by k σ₁)) (coe (rs-co n) e₁)
      :by: ap (λ — → λx, sub — (coe (rs-co n) e₁)) $
           subrel {_P_ = _==_} $ fun-ext $ sym $
           lift-lift-by~ k σ₁
    === sub (lift-by k σ₁) (λx, coe (rs-co n) e₁)
      :by: Id-refl _
    === sub (lift-by k σ₁) (coe (rs-co n) (λx, e₁))
      :by: ap (sub (lift-by k σ₁))
              (move-coe e₁ (sym $ +-suc k n))
  qed
  where σ₀ = newSub f
        σ₁ = newSub (rename ρ f)
        e₀ = rename (lift-by (k +2) ρ) e
        e₁ = rename (lift (lift-by (k +1) ρ)) e
        move-coe : ∀ {m n}
          (e : Term (m +1))
          (coer : m == n)
          → ------------------------------------
          λx, coe (ap (Term ∘ suc) coer) e
          ==
          coe (ap Term coer) (λx, e)
        move-coe e coer = subrel {_R_ = Het._==_} (
          proof λx, coe (ap (Term ∘ suc) coer) e
            het== λx, e
              :by: Id.ap2 (λ i e → λx,_ {n = i} e)
                     (sym coer)
                     (coe-eval (ap (Term ∘ suc) coer) e)
            het== coe (ap Term coer) (λx, e)
              :by: isym $ coe-eval (ap Term coer) (λx, e)
          qed)
-}
-- rename-sub {tag = term} ρ ⌊ e ⌋ f = {!!}
-- rename-sub {k = k}{m}{n}{elim} ρ (var v) f =
--   proof rename (lift-by k ρ) (sub (lift-by k σ₀) (coe (rs-co m) (var v)))
--     === rename ⦃ r = RenameableElim ⦄ (lift-by k ρ)
--           (lift-by k σ₀ (coe (ap Var $ sym $ +-suc k m) v))
--       :by: ap (rename ⦃ r = RenameableElim ⦄ (lift-by k ρ)) $
--            aux (lift-by k σ₀) v (sym $ +-suc k m)
--     === sub (lift-by k σ₁) (coe (rs-co n) e₁)
--       :by: {!rename (lift-by (k +1) ρ) (var v)!}
--   qed
--   where σ₀ = newSub f
--         σ₁ = newSub (rename ρ f)
--         e₁ = rename (lift-by (k +1) ρ) (var v)
--         aux : ∀ {k m n}
--           (σ : Sub m n)
--           (v : Var k)
--           (p : k == m)
--           → ------------------------------
--           sub σ (coe (ap Elim p) (var v))
--           ==
--           σ (coe (ap Var p) v)
--         aux σ v (Id-refl k) = subrel {_R_ = Het._==_} (
--           proof sub σ (coe (Id-refl _) (var v))
--             het== sub σ (var v)
--               :by: ap (sub σ) $ coe-eval (Id-refl _) (var v)
--             het== σ (coe (Id-refl _) v)
--               :by: ap σ $ sym $ coe-eval (Id-refl _) v
--           qed)
--         ren-lift-var : ∀ {m} k ρ f (v : Var (k + (m +1))) →
--           rename (lift-by k ρ) (lift-by k (newSub f) v)
--           == {!!}
--           -- sub (lift-by k (rename ρ (newSub f)))
--           --     (rename (lift-by (k +1) ρ) (var v))
--         ren-lift-var = {!!}
-- rename-sub {tag = elim} ρ (e ` s) f = {!!}
-- rename-sub {tag = elim} ρ (s ꞉ S) f = {!!}

open import Type.BinarySum hiding (_+_)

open Selector

lift-nthSub : ∀ {k m}
  (f : Elim m)
  (p : k < m +1)
  → --------------------------------------------------
  lift (nthSub k p f) == nthSub (k +1) (s<s p) (shift f)
lift-nthSub {k}{m} f p = subrel {_R_ = Het._==_} $ fun-ext
  λ { new → Het.refl (var new)
    ; (old v) →
        proof lift (nthSub k p f) (old v)
          het== shift (nthSub k p f v)
            :by: Het.refl _
          === nthSub (k +1) (s<s p) (shift f) (old v)
            :by: nthSub+1 f p v
        qed}
  where nthSub+1 : ∀ {k m}
          (f : Elim m)
          (p : k < m +1)
          (v : Var (m +1))
          → --------------------------------------------------------------
          shift (nthSub k p f v) == nthSub (k +1) (s<s p) (shift f) (old v)
        nthSub+1 {k} f p v with compare (index v) _<_ k ⦃ Comparable< ⦄
        nthSub+1 f p v | lt q = Id-refl _
        nthSub+1 f p v | eq q = Id-refl _
        nthSub+1 {k} f p new | gt k<0 = ⊥-recursion _ $ ¬-<0 k k<0
        nthSub+1 f p (old v) | gt q = Id-refl _
  
open import Collection hiding (_~_)
open import Data.Functor
open import Data.List as L hiding ([_]; index; _++_)
open import Data.List.Functor

nthSub-neutral : ∀ {k m}
  (f : Elim m)
  {tag}
  (e : expr-of-type tag (m +1))
  (p : k < m +1)
  (q : nth-var k p ∉ fv e)
  → --------------------------------------------------
  sub (nthSub k p f) e == del-nth k e p q
nthSub-neutral f {term} (⋆ i) p q = Id-refl (⋆ i)
nthSub-neutral {k} f {term} ([ ρ x: S ]→ T) p q =
  ap2 [ ρ x:_]→_
    (nthSub-neutral f S p λ q' → q $ ⟵ (++-prop {l' = l'}) $ ∨left q')
    (proof sub (lift (nthSub k p f)) T
       === sub (nthSub (k +1) (s<s p) (shift f)) T
         :by: ap (λ — → sub — T) $ lift-nthSub f p
       === del-nth (k +1) T (s<s p) q'
         :by: nthSub-neutral (shift f) T (s<s p) q'
     qed)
  where l' = prevRenUnsafe <$> remove new (fv T)
        q' = λ q' → q $ ⟵ extend-prop $ ∨left $ del-nth-aux {p = p} q'
nthSub-neutral {k} f {term} (λx, t) p q =
  proof sub (nthSub k p f) (λx, t)
    === λx, sub (lift (nthSub k p f)) t
      :by: Id-refl _
    === λx, sub (nthSub (k +1) (s<s p) (shift f)) t
      :by: ap (λ — → λx, sub — t) $ lift-nthSub f p
    === λx, del-nth (k +1) t (s<s p) _
      :by: ap λx,_ $
           nthSub-neutral (shift f) t (s<s p)
           (λ q' → q $ del-nth-aux {n = k}{p} q')
    === del-nth k (λx, t) p q
      :by: Id-refl _
  qed
nthSub-neutral f {term} ⌊ e ⌋ p q = ap ⌊_⌋ $ nthSub-neutral f e p q
nthSub-neutral {k} f {elim} (var v) p q
  with compare (index v) _<_ k ⦃ Comparable< ⦄
nthSub-neutral f {elim} (var v) p q | lt _ = Id-refl _
nthSub-neutral f {elim} (var v) p q | eq (Id-refl .(index v)) =
  ⊥-recursion _ $ q $
  Id.coe (ap (_∈ L.[ v ]) $ sym $ nth-var-index== v) (x∈x∷ [])
nthSub-neutral {k} f {elim} (var new) p q | gt r = ⊥-recursion _ (¬-<0 k r)
nthSub-neutral {k} f {elim} (var (old v)) p q | gt r = Id-refl (var v)
nthSub-neutral f {elim} (f' ` s) p q =
  ap2 _`_
    (nthSub-neutral f f' p λ q' → q $ ⟵ (++-prop {l' = fv s}) $ ∨left q')
    (nthSub-neutral f s p λ q' → q $ ⟵ (++-prop {l = fv f'}) $ ∨right q')
nthSub-neutral f {elim} (s ꞉ S) p q = 
  ap2 _꞉_
    (nthSub-neutral f s p λ q' → q $ ⟵ (++-prop {l' = fv S}) $ ∨left q')
    (nthSub-neutral f S p λ q' → q $ ⟵ (++-prop {l = fv s}) $ ∨right q')

open import Function.Proof
open import Data.Nat.Proof

nth-var∉shift : ∀ {tag m} k
  (e : expr-of-type tag (k + m))
  → --------------------------------------------------
  nth-var k (postfix (_+ (m +1)) k)
  ∉
  fv (rename ⦃ r = RenameableExpr ⦄ (lift-by k old) e)
nth-var∉shift {elim} k (var v) p with -∈[-]→== p
nth-var∉shift {elim}{m} k (var v) p
  | p' = nth-k≠lift-k-old-v k m (postfix (_+ (m +1)) k) v p'
  where nth-k≠lift-k-old-v : ∀ k m (p : k < k + (m +1)) v →
          nth-var k p ≠ lift-by k old v
        nth-k≠lift-k-old-v zero m p v ()
        nth-k≠lift-k-old-v (k +1) m p (old v) q with
          proof old (nth-var k (s<s→-<- p))
            === [ old ∘ old× k ∘ old , id ] ([ id + old ] (without k new v))
              :by: q
            het== [ old ∘ old× k ∘ old , old ] (without k new v)
              :by: [ old ∘ old× k ∘ old , id ]∘[ id + old ] (without k new v) 
            het== old ([ old× k ∘ old , id ] (without k new v))
              :by: sym (old ∘[ old× k ∘ old , id ]) (without k new v) 
            === old (lift-by k old v)
              :by: Id-refl _
          qed
        ... | old-nth-k==old-lift-k =
          nth-k≠lift-k-old-v k m (postfix (_+ (m +1)) k) v $
          inj old-nth-k==old-lift-k
nth-var∉shift {elim} k (f ` s) p
  with ⟶ (++-prop
             {l = fv (rename ⦃ r = RenameableElim ⦄ (lift-by k old) f)}
             {l' = fv (rename ⦃ r = RenameableTerm ⦄ (lift-by k old) s)}) p
nth-var∉shift k (f ` s) p | ∨left q = nth-var∉shift k f q
nth-var∉shift k (f ` s) p | ∨right q = nth-var∉shift k s q
nth-var∉shift {elim} k  (s ꞉ S) p
  with ⟶ (++-prop
             {l = fv (rename ⦃ r = RenameableTerm ⦄ (lift-by k old) s)}
             {l' = fv (rename ⦃ r = RenameableTerm ⦄ (lift-by k old) S)}) p
nth-var∉shift k (s ꞉ S) p | ∨left q = nth-var∉shift k s q
nth-var∉shift k (s ꞉ S) p | ∨right q = nth-var∉shift k S q
nth-var∉shift {term}{m} k ([ π x: S ]→ T) p
  with p'
  where aux : ∀{m n}
          (S' : Term n)
          (T' : Term (n +1))
          (p : n == m +1)
          → --------------------------------------------------
          fv ([ π x: S' ]→ T')
          Het.==
          fv (coe (ap Term p) S') ++
            (prevRenUnsafe <$> remove new (fv (coe (ap (Term ∘ suc) p) T')))
        coer = +-suc k m
        S' = rename ⦃ r = RenameableTerm ⦄ (lift-by k old) S
        T' = rename (lift (lift-by k old)) T
        k<k+m+1 : k < k + m +1
        k<k+m+1 = proof k
                    〉 _<_ 〉 k +1     :by: postfix suc k
                    〉 _≤_ 〉 k + m +1 :by: postfix (_+ m) (k +1)
                  qed
        p' :
          nth-var k k<k+m+1 ∈
            fv (coe (ap Term coer) S') ++
              (prevRenUnsafe <$> remove new (fv (coe (ap (Term ∘ suc) coer) T')))
        p' = Id.coe (subrel $
          Het.ap3 (λ i (v : Var i)(l : List (Var i)) → v ∈ l)
            (subrel $ +-suc k m)
            (nth-var== (+-suc k m) (Id-refl k))
            (aux S' T' coer))
            p
        aux S' T' (Id-refl (m +1)) =
          Het.ap2 (λ S T → fv ([ π x: S ]→ T))
            (sym {𝒰 = 𝒰 ⁺ ⊔ 𝒱} $ coe-eval (Id-refl _) S')
            (sym {𝒰 = 𝒰 ⁺ ⊔ 𝒱} $ coe-eval (Id-refl _) T')
nth-var∉shift {term}{m} k ([ π x: S ]→ T) p | p'
  with ⟶ (++-prop
    {l = fv (coe (ap Term coer) S')}
    {l' = prevRenUnsafe <$> remove new (fv (coe (ap (Term ∘ suc) coer) T'))})
    p'
  where coer = +-suc k m
        S' = rename ⦃ r = RenameableTerm ⦄ (lift-by k old) S
        T' = rename (lift (lift-by k old)) T
nth-var∉shift {term}{m} k ([ π x: S ]→ T) _ | _ | ∨left q =
  nth-var∉shift k S (Id.coe (
    subrel $
      Het.ap3 (λ i (v : Var i)(t : Term i) → v ∈ fv t)
        (subrel $ sym $ +-suc k m)
        (nth-var== (sym $ +-suc k m) (Id-refl k))
        (coe-eval coer S'))
    q)
  where coer : Term (k + (m +1)) == Term (k + m +1)
        coer = ap Term $ +-suc k m
        S' = rename ⦃ r = RenameableTerm ⦄ (lift-by k old) S
nth-var∉shift {term}{m} k ([ π x: S ]→ T) _ | _ | ∨right q
  with ∈fmap⁻¹ l prevRenUnsafe q
  where coer = ap Term $ +-suc (k +1) m
        l = remove new (fv (coe coer (rename (lift (lift-by k old)) T)))
nth-var∉shift {term}{m} k ([ π x: S ]→ T) _
  | _ | _ | v , (_ , q)
  with ⟶ (remove-valid
    {y = new}
    {fv (coe coer (rename (lift-by (k +1) old) T))})
    (Id.coe (ap (λ — → v ∈ remove new (fv (coe coer (rename — T)))) $
             subrel $ fun-ext $ lift-lift-by~ k old) q)
  where coer = ap Term $ +-suc (k +1) m
nth-var∉shift k ([ π x: S ]→ T) _ | _ | _ | new , _ | _ , new≠new =
  ⊥-recursion _ $ new≠new $ Id-refl new
nth-var∉shift {m = m} k ([ π x: S ]→ T) _
  | _ | _ | (old v) , (v==nth-k , q) | old-v∈fv , _ =
  nth-var∉shift (k +1) T $
  aux (nth-var (k +1) (postfix (_+ (m +1)) (k +1))) $
  Id.ap2 (λ i v → old {i} v) (sym $ +-suc k m) (
  proof v
    === nth-var {k + m +1} k _
      :by: v==nth-k
    het== nth-var {k + (m +1)} k _
      :by: nth-var== (sym $ +-suc k m) (Id-refl k)
  qed)
  where aux :
          (w : Var (k + (m +1) +1))
          (p' : old v Het.== w) 
          → --------------------------------------------------
          w ∈ fv (rename (lift-by (k +1) old) T)
        aux w p' = Id.coe (
          subrel $ Het.ap3 (λ i (v : Var i)(t : Term i) → v ∈ fv t)
            (subrel $ sym $ +-suc (k +1) m)
            p'
            (coe-eval (ap Term $ +-suc (k +1) m) (rename (lift-by (k +1) old) T)))
          old-v∈fv
nth-var∉shift {term}{m} k (λx, f) p with ∈fmap⁻¹ l prevRenUnsafe aux
  where p' : k < k + m +1
        coer = ap Term $ +-suc (k +1) m
        l = remove new (fv (coe coer (rename (lift-by (k +1) old) f)))
        aux : nth-var k p' ∈ prevRenUnsafe <$> l
        open import Proposition.Sum
        aux = Id.coe (subrel $ Het.ap3
                (λ m (v : Var m)(l : List (Var m)) → v ∈ l)
                (subrel $ +-suc k m)
                (ap (λ {(m , p) → nth-var {m} k p}) (Σₚ== $ +-suc k m))
                (proof fv {tag = term} (
                          rename ⦃ r = RenameableTerm ⦄ (lift-by k old) (λx, f))
                   === fv (λx, rename (lift (lift-by k old)) f)
                     :by: Id-refl _
                   het== fv (λx, rename (lift-by (k +1) old) f)
                     :by: ap (λ — → fv (λx, rename — f)) $
                          fun-ext $ lift-lift-by~ k old
                   het== fv (λx, coe coer (rename (lift-by (k +1) old) f))
                     :by: Id.ap2 (λ n t → fv (λx,_ {n} t))
                            (+-suc k m)
                            (isym $
                             coe-eval coer (rename (lift-by (k +1) old) f))
                   === prevRenUnsafe <$>
                       remove new (fv (
                         coe coer (rename (lift-by (k +1) old) f)))
                     :by: Id-refl _
                 qed))
              p
        p' = proof k
               〉 _≤_ 〉 k + m    :by: postfix (_+ m) k
               〉 _<_ 〉 k + m +1 :by: postfix _+1 (k + m)
             qed
nth-var∉shift {m = m} k (λx, f) p | v , (_ , q)
  with ⟶ (remove-valid
    {y = new}
    {fv (coe (ap Term $ +-suc (k +1) m) (rename (lift-by (k +1) old) f))})
    q
nth-var∉shift k (λx, f) p | new , _ | _ , new≠new =
  ⊥-recursion _ $ new≠new $ Id-refl new
nth-var∉shift {m = m} k (λx, f) p | (old v) , (v==nth-k , q) | old-v∈fv , _ =
  nth-var∉shift (k +1) f $
  aux (nth-var (k +1) (postfix (_+ (m +1)) (k +1))) $
  Id.ap2 (λ i v → old {i} v) (sym $ +-suc k m) (
  proof v
    === nth-var {k + m +1} k _
      :by: v==nth-k
    het== nth-var {k + (m +1)} k _
      :by: nth-var== (sym $ +-suc k m) (Id-refl k)
  qed)
  where aux :
          (w : Var (k + (m +1) +1))
          (p' : old v Het.== w) 
          → --------------------------------------------------
          w ∈ fv (rename (lift-by (k +1) old) f)
        aux w p' = Id.coe (
          subrel $ Het.ap3 (λ i (v : Var i)(t : Term i) → v ∈ fv t)
            (subrel $ sym $ +-suc (k +1) m)
            p'
            (coe-eval (ap Term $ +-suc (k +1) m) (rename (lift-by (k +1) old) f)))
          old-v∈fv
nth-var∉shift {term} k ⌊ e ⌋ p = nth-var∉shift k e p

sub-newSub :
  (σ : Sub m n)
  (f : Elim m)
  → --------------------------------------------------
  sub σ ∘ newSub f == sub (newSub (sub σ f)) ∘ lift σ
sub-newSub {m}{n} σ f = subrel {_R_ = Het._==_} $ fun-ext
  λ { new → Het.refl (sub σ f)
    ; (old v) →
      proof sub σ (newSub f (old v))
        het== σ v
          :by: Het.refl (σ v)
        === del-nth 0 (shift (σ v)) (z<s _) (nth-var∉shift 0 (σ v))
          :by: sym {𝒰 = 𝒰 ⁺ ⊔ 𝒱} $
               del-0-shift~id (σ v) (nth-var∉shift 0 (σ v))
        === sub (newSub (sub σ f)) (shift (σ v))
          :by: sym {𝒰 = 𝒰 ⁺ ⊔ 𝒱} $
               nthSub-neutral (sub σ f) (shift (σ v)) (z<s n) _
        === sub (newSub (sub σ f)) (lift σ (old v))
          :by: Id-refl _
      qed}
  where del-0-shift~id : ∀ {m tag}
          (e : expr-of-type tag m)
          (q : new ∉ fv (shift e))
          → ----------------------------------------
          del-nth 0 (shift e) (z<s m) q == e
        del-0-shift~id {zero}{tag} e q = {!!}
        del-0-shift~id {m +1} e q = {!!}

rename-[-/new] :
  (ρ : Ren m n)
  (e : expr-of-type tag (m +1))
  (f : Elim m)
  → --------------------------------------------------------------
  rename ⦃ r = RenameableExpr ⦄ ρ (e [ f /new])
  ==
  rename (lift ρ) e [ rename ⦃ r = RenameableExpr ⦄ ρ f /new]
rename-[-/new] ρ e f = {!!}
-- subrel {_R_ = Het._==_} (
--   proof rename ρ (e [ f /new])
--     het== rename (lift-by 0 ρ) (e [ f /new])
--       :by: ap (λ — → rename — (e [ f /new])) $
--            fun-ext $ sym $ lift-by-0~id ρ
--     het== rename (lift-by 0 ρ) (sub (lift-by 0 (newSub f)) e)
--       :by: ap (λ — → rename (lift-by 0 ρ) (sub — e)) $
--            fun-ext $ sym $ lift-by-0~id (newSub f)
--     === sub (lift-by 0 (rename ρ ∘ newSub f)) e
--       :by: rename-sub {k = 0} ρ (newSub f) e
--     het== sub (lift-by 0 (newSub (rename ρ f))) (rename (lift ρ) e)
--       :by: {!rename-sub {k = 0} ρ (newSub f) e!}
--     het== rename (lift ρ) e [ rename ρ f /new]
--       :by: ap (λ — → sub — (rename (lift ρ) e)) $
--            fun-ext $ lift-by-0~id (newSub (rename ρ f))
--   qed)
  -- where rename-newSub : ∀ {m n}
  --         (ρ : Ren m n)
  --         (f : Elim m)
  --         → ----------------------------------------
  --         lift-by 0 (rename ρ ∘ newSub f)
  --         ==
  --         {!lift-by 0 (newSub (rename ρ f))!}
  --       rename-newSub = {!!}

{-
rename-[-/new] ρ e f = subrel {_R_ = Het._==_} (
  proof rename ρ (e [ f /new])
    het== rename (lift-by 0 ρ) (e [ f /new])
      :by: ap (λ — → rename — (e [ f /new])) $
           fun-ext $ sym $ lift-by-0~id ρ
    het== rename (lift-by 0 ρ) (sub (lift-by 0 (newSub f)) e)
      :by: ap (λ — → rename (lift-by 0 ρ) (sub — e)) $
           fun-ext $ sym $ lift-by-0~id (newSub f)
    het== rename (lift-by 0 ρ) (sub (lift-by 0 (newSub f)) (coe (Id-refl _) e))
      :by: ap (rename (lift-by 0 ρ) ∘ sub (lift-by 0 (newSub f))) $
           sym {R = Het._==_} $ coe-eval (Id-refl _) e
    === sub (lift-by 0 (newSub (rename ρ f)))
            (coe (Id-refl _) (rename (lift-by 1 ρ) e))
      :by: rename-sub ρ e f
    het== sub (lift-by 0 (newSub (rename ρ f))) (rename (lift ρ) e)
      :by: ap (sub (lift-by 0 (newSub (rename ρ f)))) $
           coe-eval (Id-refl _) (rename (lift-by 1 ρ) e)
    het== rename (lift ρ) e [ rename ρ f /new]
      :by: ap (λ — → sub — (rename (lift ρ) e)) $
           fun-ext $ lift-by-0~id (newSub (rename ρ f))
  qed)
-}

{-
* original:

rename ρ (e [ f /new])
==
rename (lift ρ) e [ rename ρ f /new]

* for k = 0 (original, rephrased):

rename (lift-by 0 ρ) (sub (nthSub 0 _ f) e)
==
sub (newSub (rename ρ f)) (rename (lift-by 1 ρ) e)

* for k = 1
rename (lift ρ) (sub (lift-by 1 (newSub f)) t)
==?==
sub (lift-by 1 (newSub (rename ρ f))) (rename (lift-by 2 ρ) t)

* generalised:

rename (lift-by k ρ) (sub (lift-by k (new-Sub f)) e)
==
sub (lift-by k (newSub (rename ρ f))) (rename (lift-by (k +1) ρ) e)
-}
