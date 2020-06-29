{-# OPTIONS --exact-split --prop #-} -- TODO: fix del-k-shift~id λx,_ case
open import Basic using (Rig; wfs)
open import PropUniverses

module Substitution.Property.NthVarAuxiliary
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

open import Collection hiding (_~_)
open import Data.Functor
open import Data.Monad
open import Data.List as L hiding ([_]; index; _++_)
open import Data.List.Functor

open import Function.Proof
open import Data.Nat.Proof

private
  k+1≤k+m+1 : ∀ k m → k +1 ≤ k + (m +1)

k+1≤k+m+1 k m =
  proof k +1
    〉 _≤_ 〉 k + m +1 :by: postfix (_+ m) (k +1)
    === k + (m +1)  :by: sym $ +-suc k m
  qed

nth-var∉shift : ∀ {tag m} k
  (e : expr-of-type tag (k + m))
  → --------------------------------------------------
  nth-var k (k+1≤k+m+1 k m)
  ∉
  fv (rename ⦃ r = RenameableExpr ⦄ (lift-by k old) e)
nth-var∉shift {elim} k (var v) p with ⟶ -∈[-]↔== p
nth-var∉shift {elim}{m} k (var v) p
  | p' = nth-k≠lift-k-old-v k m v p'
  where nth-k≠lift-k-old-v : ∀ k m v →
          nth-var k (k+1≤k+m+1 k m) ≠ lift-by k old v
        nth-k≠lift-k-old-v zero m v ()
        nth-k≠lift-k-old-v (k +1) m (old v) q =
          nth-k≠lift-k-old-v k m v $
          inj $ subrel q
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
            (fv (coe (ap (Term ∘ suc) p) T') >>= prevSafe)
        coer = +-suc k m
        S' = rename ⦃ r = RenameableTerm ⦄ (lift-by k old) S
        T' = rename (lift (lift-by k old)) T
        p' :
          nth-var k (postfix (_+ m) (k +1)) ∈
            fv (coe (ap Term coer) S') ++
              (fv (coe (ap (Term ∘ suc) coer) T') >>= prevSafe)
        p' = Id.coe (subrel $
          Het.ap3 (λ i (v : Var i)(l : List (Var i)) → v ∈ l)
            (+-suc k m)
            (nth-var== (k+1≤k+m+1 k m) (+-suc k m) (Id.refl k))
            (aux S' T' coer))
            p
        aux S' T' (Id.refl (m +1)) =
          Het.ap2 (λ S T → fv ([ π x: S ]→ T))
            (sym {𝒰 = 𝒰 ⁺ ⊔ 𝒱} $ coe-eval (Id.refl _) S')
            (sym {𝒰 = 𝒰 ⁺ ⊔ 𝒱} $ coe-eval (Id.refl _) T')
nth-var∉shift {term}{m} k ([ π x: S ]→ T) p | p'
  with ⟶ (++-prop
    {l = fv (coe (ap Term coer) S')}
    {l' = fv (coe (ap (Term ∘ suc) coer) T') >>= prevSafe})
    p'
  where coer = +-suc k m
        S' = rename ⦃ r = RenameableTerm ⦄ (lift-by k old) S
        T' = rename (lift (lift-by k old)) T
nth-var∉shift {term}{m} k ([ π x: S ]→ T) _ | _ | ∨left q =
  nth-var∉shift k S (Id.coe (
    subrel $
      Het.ap3 (λ i (v : Var i)(t : Term i) → v ∈ fv t)
        (sym $ +-suc k m)
        (nth-var== (postfix (_+ m) (k +1)) (sym $ +-suc k m) (Id.refl k))
        (coe-eval coer S'))
    q)
  where coer : Term (k + (m +1)) == Term (k + m +1)
        coer = ap Term $ +-suc k m
        S' = rename ⦃ r = RenameableTerm ⦄ (lift-by k old) S
nth-var∉shift {term}{m} k ([ π x: S ]→ T) _ | _ | ∨right q
  with ⟶ (∈bind (nth-var k (postfix (_+ m) (k +1)))
                  prevSafe
                  (fv (coe (ap Term $ +-suc (k +1) m) T')))
           q
  where T' = rename (lift (lift-by k old)) T
nth-var∉shift {term} {m} k ([ π x: S ]→ T) _
  | _ | ∨right q | old v , (old-v∈fv-T' , x∈x∷ []) =
  nth-var∉shift (k +1) T $
  Id.coe (
    subrel $
    Het.ap3 (λ i (v : Var i)(t : Term i) → v ∈ fv t)
      (sym $ +-suc (k +1) m)
      (nth-var== (postfix (_+ m) (k +2)) (sym $ +-suc (k +1) m) (Id.refl (k +1)))
      (proof coe coer T'
        het== T'
          :by: coe-eval coer T'
        het== rename (lift-by (k +1) old) T
          :by: ap (λ — → rename — T) $ fun-ext $
               lift-lift-by~ k old
       qed)) $
  old-v∈fv-T'
  where T' = rename (lift (lift-by k old)) T
        coer = ap Term $ +-suc (k +1) m
nth-var∉shift {term}{m} k (λx, t) p with ⟶ (∈bind v prevSafe (fv t')) p
  where v = nth-var k (k+1≤k+m+1 k m)
        t' = rename (lift (lift-by k old)) t
nth-var∉shift {term} {m} k (λx, t) p | old v , (old-v∈fv-t' , x∈x∷ []) =
  nth-var∉shift (k +1) t $
  Id.coe (ap (λ — → old v ∈ fv (rename — t)) $
          subrel $ fun-ext $
          lift-lift-by~ k old)
  old-v∈fv-t'
nth-var∉shift {term} k ⌊ e ⌋ p = nth-var∉shift k e p

private
  delVar== : ∀ {m} k v (v' : Var (k + m +1))
    (p : v' Het.== lift-by {m = m} k old v)
    (q : nth-var k (postfix (_+ m) (k +1)) ≠ v')
    →
    delVar k v' (postfix (_+ m) k) q Het.== v

delVar== zero v (old v) (Het.refl (old v)) q = Het.refl v
delVar== (k +1) new new p q = Het.refl new
delVar== (k +1) (old v) new p q with lemma k v
  where lemma : ∀ k (v : Var (k + m))
          → -------------------------------------------
          ∃ λ (v' : Var (k + (m +1))) →
            lift-by (k +1) old (old v) == old v'
        lemma zero v = old v , Id.refl _
        lemma (k +1) new = default , Id.refl _
        lemma (k +1) (old v) =
          lift-by (k +1) old (old v) ,
          subrel {_R_ = Het._==_}{_P_ = _==_} $ sym $
          lift-lift-by~ (k +1) old (old (old v))
delVar== {m}(k +1)(old v) new p q | v' , p' =
  ⊥-recursion _ $ new≠old _ v' (sym $ +-suc k m) p″
  where p″ : new Het.== old v'
        p″ = proof new
               het== lift-by (k +1) old (old v) :by: p
                 === old v'                       :by: p'
               qed
-- delVar== {m}(k +1) (old v) new p q | v' , p' | new==old-v' =
--   ? -- 
delVar== {m}(k +1) new (old v') p q =
  ⊥-recursion _ $ new≠old _ v' (+-suc k m) (isym p)
delVar== {m}(k +1) (old v) (old v') p q =
  ap old $ delVar== k v v'
    (old==old→== (sym $ +-suc k m) aux)
    λ q' → q $ ap old q'
  where aux : old v' Het.== old (lift-by k old v)
        aux = proof old v'
                het== lift-by (k +1) old (old v)
                  :by: p
                het== lift (lift-by k old) (old v)
                  :by: sym $ lift-lift-by~ k old (old v)
                === old (lift-by k old v)
                  :by: Id.refl _
              qed

open import Proposition.Sum

private
  ren = λ {m}{tag} k → rename ⦃ r = RenameableExpr {tag} ⦄ (lift-by {m = m} k old)

del-k-shift~id : ∀ {m tag} k
  (e : expr-of-type tag (k + m)) →
  let coer = ap (expr-of-type tag) $ +-suc k m
      e' = coe coer (ren k e)
  in
  (q : nth-var k (postfix (_+ m) (k +1)) ∉ fv e')
  → --------------------------------------------------
  del-nth k e' (postfix (_+ m) k) q == e
del-k-shift~id {m}{term} k (⋆ i) q =
  proof del-nth k (coe (ap Term $ +-suc k m) (⋆ i)) (postfix (_+ m) k) q
    === del-nth k (⋆ i) (postfix (_+ m) k) (λ ())
      :by: subrel {_P_ = _==_} $
           del-nth== (Id.refl term)(Id.refl (k + m))(Id.refl k)
             (proof coe (ap Term $ +-suc k m) (⋆ i)
                het== ⋆ i :by: coe-eval (ap Term $ +-suc k m) (⋆ i)
                het== ⋆ i
                  :by: ap (λ — → ⋆ {n = —} i) ⦃ Relating-all-==-het== ⦄ $
                       +-suc k m
              qed)
    === ⋆ i :by: Id.refl _
  qed
del-k-shift~id {m}{term} k ([ π x: S ]→ T) q =
  proof del-nth k (coe coer ([ π x: ren k S ]→ rename (lift (lift-by k old)) T))
                  (postfix (_+ m) k) q
    === del-nth k
          (coe coer ([ π x: ren k S ]→ ren (k +1) T))
          (postfix (_+ m) k)
          q₀
      :by: ap (λ (— : Σₚ λ ρ → v ∉ fv (coe coer ([ π x: ren k S ]→ rename ρ T))) →
              del-nth k (coe coer ([ π x: ren k S ]→ rename (elem —) T))
                        (postfix (_+ m) k) (prop —)) $
           Σₚ== {σ = _ , q}{ρ = _ , q₀} step₀
    === del-nth k ([ π x: coe coer (ren k S) ]→
                     coe (ap Term $ +-suc (k +1) m) (ren (k +1) T))
                  (postfix (_+ m) k) q₁
      :by: ap (λ (— : Σₚ λ e → v ∉ fv e) →
                 del-nth k (elem —) (postfix (_+ m) k) (prop —)) $
           Σₚ== {σ = _ , q₀}{ρ = _ , q₁} move-coe
    === [ π x: del-nth k (coe coer (ren k S)) (postfix (_+ m) k) _ ]→
          del-nth (k +1) (coe (ap Term $ +-suc (k +1) m) (ren (k +1) T))
                  (postfix (_+ m) (k +1)) _
      :by: Id.refl _
    === [ π x: S ]→ T
      :by: ap2 [ π x:_]→_
             (del-k-shift~id k S _)
             (del-k-shift~id (k +1) T _)
  qed
  where v = nth-var k (postfix (_+ m) (k +1))
        coer = ap Term $ +-suc k m
        step₀ = subrel {_P_ = _==_} $ fun-ext $ lift-lift-by~ k old
        move-coe :
          coe coer ([ π x: ren k S ]→ ren (k +1) T)
          ==
          [ π x: coe coer (ren k S) ]→
            coe (ap Term $ +-suc (k +1) m) (ren (k +1) T)
        move-coe = subrel {_P_ = _==_} (
          proof coe coer ([ π x: ren k S ]→ ren (k +1) T)
           het== [ π x: ren k S ]→ ren (k +1) T
            :by: coe-eval coer ([ π x: ren k S ]→ ren (k +1) T)
           het== [ π x: coe coer (ren k S) ]→
                   coe (ap Term $ +-suc (k +1) m) (ren (k +1) T)
            :by: Het.ap3 (λ i (S : Term i)(T : Term (i +1)) → [ π x: S ]→ T)
                   (+-suc k m)
                   (isym $ coe-eval coer (ren k S))
                   (isym $ coe-eval (ap Term $ +-suc (k +1) m) (ren (k +1) T))
          qed)
        q₀ = Id.coe
          (ap (λ — → v ∉ fv (coe coer ([ π x: ren k S ]→ rename — T))) step₀)
          q
        q₁ = Id.coe (ap (λ — → v ∉ fv —) move-coe) q₀
del-k-shift~id {m}{term} k (λx, t) q =
  proof del-nth k (coe (ap Term $ +-suc k m) (ren k (λx, t)))
                (postfix (_+ m) k) q
    === λx, del-nth (k +1)
                (coe (ap Term $ +-suc (k +1) m) (ren (k +1) t))
                (postfix (_+ m) (k +1)) q'
      :by: move-coe (coe (ap Term $ +-suc k m) (ren k (λx, t)))
             (coe (ap Term $ +-suc (k +1) m) (ren (k +1) t))
             (postfix (_+ m) k) q q' (
               proof coe (ap Term $ +-suc k m) (ren k (λx, t))
                 het== ren k (λx, t)
                   :by: coe-eval (ap Term $ +-suc k m) (ren k (λx, t))
                 === λx, rename (lift (lift-by k old)) t
                   :by: Id.refl _
                 het== λx, rename (lift-by (k +1) old) t
                   :by: ap (λ — → λx, rename — t) $
                        fun-ext $ lift-lift-by~ k old
                 het== λx, coe (ap Term $ +-suc (k +1) m) (ren (k +1) t)
                   :by: Id.ap2 (λ i (t : Term (i +1)) → λx, t)
                          (+-suc k m)
                          (isym $
                           coe-eval (ap Term $ +-suc (k +1) m) (ren (k +1) t))
               qed)
    === λx, t
      :by: ap λx,_ $ del-k-shift~id (k +1) t q'
  qed
  where move-coe : ∀{k m}
          (t : Term (m +1))
          (t' : Term (m +2))
          (p : k ≤ m)
          (q : nth-var k (ap suc p) ∉ fv t)
          (q' : nth-var (k +1) (ap _+2 p) ∉ fv t')
          (eq : t Het.== λx, t')
          → --------------------------------------------------
          del-nth k t p q == λx, del-nth (k +1) t' (ap suc p) q'
        move-coe (λx, t') t' p q q' (Het.refl _) = Id.refl _
        fv==fv : fv {m = k + m +2} Het.== fv {m = k + (m +1) +1}
        t' = rename (lift (lift-by k old)) t
        q' : nth-var (k +1) (postfix (_+ m) (k +2))
             ∉
             fv (coe (ap Term $ +-suc (k +1) m) (ren (k +1) t))
        q' p with ∈map⁻¹ (fv (ren k (λx, t))) old
                    (∈fv-λ v p' (index-nth-var (k +1) pv))
          where pv = k+1≤k+m+1 (k +1) m
                v = nth-var (k +1) pv
                p' : v ∈ fv (ren (k +1) t)
                p' = Id.coe (subrel $
                  Het.ap3 (λ i (v : Var i)(t : Term i) → v ∈ fv t)
                    (sym $ +-suc (k +1) m)
                    (nth-var== (postfix (_+ m) (k +2))
                               (sym $ +-suc (k +1) m)
                               (Id.refl (k +1)))
                    (coe-eval (ap Term $ +-suc (k +1) m) (ren (k +1) t))) p
                ∈fv-λ :
                  (v : Var (k + (m +1) +1))
                  (p : v ∈ fv (ren (k +1) t))
                  (q : index v == k +1)
                  → ----------------------------------------
                  v ∈ old <$> (fv t' >>= prevSafe)
                ∈fv-λ (old v) p q =
                  ∈map old $
                  ⟵ (∈bind v prevSafe (fv t')) $
                  (old v , (
                    Id.coe (ap (λ — → old v ∈ fv (rename — t)) $
                            sym $ subrel {_P_ = _==_} $ fun-ext $
                            lift-lift-by~ k old) p ,
                    x∈x∷ []))
        q' p | v , (old-v==nth-k+1 , v∈fv-λx,t) =
          q $
          Id.coe (
            subrel $ Het.ap3 (λ i (v : Var i)(t : Term i) → v ∈ fv t)
              (+-suc k m)
              (old==old→== (+-suc k m) (
                 proof old v
                   === old (nth-var k (k+1≤k+m+1 k m))
                     :by: old-v==nth-k+1 [: _==_ ]
                   het== old (nth-var k (postfix (_+ m) (k +1)))
                     :by: nth-var== (k+1≤k+m+1 (k +1) m)
                                    (+-suc (k +1) m)
                                    (Id.refl (k +1))
                 qed))
              (isym $ coe-eval (ap Term $ +-suc k m) (λx, t')))
            v∈fv-λx,t
        fv==fv = ap (λ i → fv {m = i}{term}) $
                 subrel {_P_ = Het._==_} $ sym $
                 +-suc (k +1) m
del-k-shift~id {m}{term} k ⌊ e ⌋ q =
  proof del-nth k (coe (ap Term p) (⌊ e' ⌋)) (postfix (_+ m) k) q
    ===  del-nth k (⌊ coe (ap Elim p) e' ⌋)
                   (postfix (_+ m) k)
                   (Id.coe
                     (ap (λ — → nth-var k (postfix (_+ m) (k +1)) ∉ fv —)
                         move-coe)
                    q)
      :by: subrel {𝒰 = 𝒰 ⁺ ⊔ 𝒱}{𝒰 ⁺ ⊔ 𝒱} $
           del-nth== (Id.refl term)(Id.refl (k + m))(Id.refl k)
             (subrel {𝒰 = 𝒰 ⁺ ⊔ 𝒱}{𝒰 ⁺ ⊔ 𝒱} move-coe)
    === ⌊ e ⌋
      :by: ap ⌊_⌋ $ del-k-shift~id k e _
  qed
  where p = +-suc k m
        e' = rename ⦃ r = RenameableElim ⦄ (lift-by k old) e
        move-coe :
          coe (ap Term p) (⌊ e' ⌋) == ⌊ coe (ap Elim p) e' ⌋
        move-coe = subrel {_R_ = Het._==_} (
          proof coe (ap Term p) (⌊ e' ⌋)
            het== ⌊ e' ⌋
              :by: coe-eval (ap Term p) ⌊ e' ⌋
            het== ⌊ coe (ap Elim p) e' ⌋
              :by: Id.ap2 (λ i (t : Elim i) → ⌊ t ⌋)
                     p (isym $ coe-eval (ap Elim p) e')
          qed)
del-k-shift~id {m}{elim} k (var v) q =
  proof del-nth k (coe (ap Elim p) (var v')) (postfix (_+ m) k) q
    === del-nth k (var (coe (ap Var p) v'))
                  (postfix (_+ m) k)
                  q'
      :by: subrel {𝒰 = 𝒰 ⁺ ⊔ 𝒱}{𝒰 ⁺ ⊔ 𝒱} $
           del-nth== (Id.refl elim)(Id.refl (k + m))(Id.refl k)
             (subrel {𝒰 = 𝒰 ⁺ ⊔ 𝒱}{𝒰 ⁺ ⊔ 𝒱} move-coe)
    === var v
      :by: ap var $ subrel {_R_ = Het._==_}{_P_ = _==_} $
           delVar== k v (coe (ap Var p) v') (coe-eval (ap Var p) v')
             (λ {x → q (Id.coe (ap (nth-var k (postfix (_+ m) (k +1)) ∈_) $
                               sym {R = _==_} $ ap fv move-coe) $
                     ⟵ -∈[-]↔== x)})
  qed
  where p = +-suc k m
        v' = lift-by k old v
        move-coe :
          coe (ap Elim p) (var v') == var (coe (ap Var p) v')
        move-coe = subrel {_R_ = Het._==_}{_P_ = _==_} (
          proof coe (ap Elim p) (var v')
            het== var v'
              :by: coe-eval (ap Elim p) (var v')
            het== var (coe (ap Var p) v')
              :by: Id.ap2 (λ i (v : Var i) → var v)
                     (+-suc k m)
                     (isym $ coe-eval (ap Var p) v')
          qed)
        q' =
          Id.coe
            (ap (λ — → nth-var k (postfix (_+ m) (k +1)) ∉ fv —)
                move-coe)
            q
del-k-shift~id {m}{elim} k (f ` s) q =
  proof del-nth k (coe coer (ren k f ` ren k s))
                  (postfix (_+ m) k) q
    === del-nth k (coe coer (ren k f) ` coe (ap Term $ +-suc k m) (ren k s))
                  (postfix (_+ m) k) q'
      :by: ap (λ (— : Σₚ λ e → v ∉ fv e) →
                 del-nth k (elem —) (postfix (_+ m) k) (prop —)) $
           Σₚ== {σ = _ , q}{ρ = _ , q'} move-coe
    === del-nth k (coe coer (ren k f)) (postfix (_+ m) k) _ ` 
        del-nth k (coe (ap Term $ +-suc k m) (ren k s)) (postfix (_+ m) k) _
      :by: Id.refl _
    === f ` s
      :by: ap2 _`_ (del-k-shift~id k f _) (del-k-shift~id k s _)
  qed
  where v = nth-var k (postfix (_+ m) (k +1))
        coer = ap Elim $ +-suc k m
        move-coe : coe coer (ren k f ` ren k s)
                   ==
                   coe coer (ren k f) ` coe (ap Term $ +-suc k m) (ren k s)
        move-coe = subrel {_P_ = _==_} (
          proof coe coer (ren k f ` ren k s)
            het== ren k f ` ren k s
              :by: coe-eval coer (ren k f ` ren k s)
            het== coe coer (ren k f) ` coe (ap Term $ +-suc k m) (ren k s)
              :by: Het.ap3 (λ i (f : Elim i)(s : Term i) → f ` s)
                           (+-suc k m)
                           (isym $ coe-eval coer (ren k f))
                           (isym $ coe-eval (ap Term $ +-suc k m) (ren k s))
          qed)
        q' = Id.coe (ap (λ — → v ∉ fv —) move-coe) q
del-k-shift~id {m}{elim} k (s ꞉ S) q =
  proof del-nth k (coe coer (ren k s ꞉ ren k S))
                  (postfix (_+ m) k) q
    === del-nth k (coe coer' (ren k s) ꞉ coe coer' (ren k S))
                  (postfix (_+ m) k) q'
      :by: ap (λ (— : Σₚ λ e → v ∉ fv e) →
                 del-nth k (elem —) (postfix (_+ m) k) (prop —))
              (Σₚ== {σ = _ , q}{ρ = _ , q'} move-coe)
    === del-nth k (coe coer' (ren k s)) (postfix (_+ m) k) _ ꞉ 
        del-nth k (coe coer' (ren k S)) (postfix (_+ m) k) _
      :by: Id.refl _
    === s ꞉ S
      :by: ap2 _꞉_ (del-k-shift~id k s _) (del-k-shift~id k S _)
  qed
  where v = nth-var k (postfix (_+ m) (k +1))
        coer = ap Elim $ +-suc k m
        coer' = ap Term $ +-suc k m
        move-coe : coe coer (ren k s ꞉ ren k S)
                   ==
                   coe (ap Term $ +-suc k m) (ren k s) ꞉
                   coe (ap Term $ +-suc k m) (ren k S)
        move-coe = subrel {_P_ = _==_} (
          proof coe coer (ren k s ꞉ ren k S)
            het== ren k s ꞉ ren k S
              :by: coe-eval coer (ren k s ꞉ ren k S)
            het== coe coer' (ren k s) ꞉ coe coer' (ren k S)
              :by: Het.ap3 (λ i (s S : Term i) → s ꞉ S)
                           (+-suc k m)
                           (isym $ coe-eval coer' (ren k s))
                           (isym $ coe-eval coer' (ren k S))
          qed)
        q' = Id.coe (ap (λ — → v ∉ fv —) move-coe) q
