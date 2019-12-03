{-# OPTIONS --prop  #-}
module Foundations.Algebra.GroupLike where

open import Foundations.Algebra.Relations.Classes
open import Foundations.Equality.Core using (_==_; proof_)
open import Foundations.Functions.Classes using (_`_)
open import Foundations.Logic using (_∧_; ∃)
open import Foundations.Univ using (𝑙)

private
  variable
    A : Set 𝑙
    r : A → A → A
    a b c : A

record Magma (A : Set 𝑙) (_+_ : A → A → A) : Set 𝑙 where

infixl 20 _+_
_+_ : {{_ : Magma A r}} (a : A) (b : A) → A
_+_ {r = r} a b = r a b

record Commutative (A : Set 𝑙) (_+_ : A → A → A) : Set 𝑙 where
  field
    {{magma}} : Magma A _+_
    +comm : a + b == b + a

open Commutative {{...}} public hiding (magma)

record Semigroup (A : Set 𝑙) (_+_ : A → A → A) : Set 𝑙 where
  field
    {{magma}} : Magma A _+_
    +assoc : a + (b + c) == (a + b) + c

open Semigroup {{...}} public hiding (magma)

record Monoid (A : Set 𝑙) (_+_ : A → A → A) : Set 𝑙 where
  field
    {{semigroup}} : Semigroup A _+_
    zero : A
    +zero : a + zero == a
    zero+ : zero + a == a

open Monoid {{...}} public hiding (semigroup)

+swap :
  {{_ : Monoid A r}}
  {{_ : Commutative A r}}
  {a b c : A}
  → ------------------------
  a + (b + c) == b + (a + c)
+swap {a = a} {b} {c} =
  proof
    ?
  qed
  -- proof
  --   a + (b + c) 〉 _==_ 〉 a + b + c :by: +assoc
  --     〉 _==_ 〉 b + a + c           :by: _+ c ` +comm
  --     〉 _==_ 〉 b + (a + c)         :by: ← +assoc -- ← +assoc
    -- 〈 _==_ 〉-[ +assoc ]
    -- a + b + c
    -- 〈 _==_ 〉-[ _+ c ` +comm ]
    -- b + a + c
    -- 〈 _==_ 〉-[ ← +assoc ]
    -- b + (a + c)
  -- qed

record Group (A : Set 𝑙) (_+_ : A → A → A) : Set 𝑙 where
  field
    {{monoid}} : Monoid A _+_
    ∃inverse : ∃ b ∶ A , a + b == zero ∧ b + a == zero

open Group {{...}} public hiding (monoid)
