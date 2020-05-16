{-# OPTIONS --exact-split --prop #-} -- TODO: add --safe
open import Basic using (Rig; wfs)
open import PropUniverses

module Substitution.Property.CommuteAuxiliary
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

open import Proposition.Identity.Coercion
open import Axiom.FunctionExtensionality

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

sub-neutral : ∀ {k m}
  (f : Elim k)
  {tag}
  (e : expr-of-type tag m)
  (p : k < m +1)
  (q : nth-var k p ∉ fv e)
  → --------------------------------------------------
  sub (nthSub k p f) (rename (lift-by k old) e) == e
sub-neutral = ?


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
          :by: ?
        === sub (newSub (sub σ f)) (shift (σ v))
          :by: sym {𝒰 = 𝒰 ⁺ ⊔ 𝒱} $
               nthSub-neutral (sub σ f) (shift (σ v)) (z<s n) _
        === sub (newSub (sub σ f)) (lift σ (old v))
          :by: Id-refl _
      qed}

rename-[-/new] :
  (ρ : Ren m n)
  (e : expr-of-type tag (m +1))
  (f : Elim m)
  → --------------------------------------------------------------
  rename ⦃ r = RenameableExpr ⦄ ρ (e [ f /new])
  ==
  rename (lift ρ) e [ rename ⦃ r = RenameableExpr ⦄ ρ f /new]
rename-[-/new] ρ e f = {!!}
