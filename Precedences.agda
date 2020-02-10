module Precedences where

-- TypeTheory (200 - 150)

infix 180 _[_/—] -- TypeTheory.Computation
infix 180 _[_/new] -- TypeTheory.Computation
infix 170 [_x:_]→_ λx,_ -- TypeTheory.Syntax
infix 160 _`_ _꞉_ -- TypeTheory.Syntax
infixl 155 _∥x:_ -- TypeTheory.Context
infixl 155 _∥_,x:_ -- TypeTheory.Context
infixl 154 _pt+_ -- TypeTheory.Context
infixl 153 _++_ -- TypeTheory.Context
infix 152 _⊢_∋_ _⊢_∈_ _⊢₀_∋_ -- TypeTheory.Judgment
infix 152 _⊢_,_∋_ _⊢_,_∈_ _⊢₀_∋_ -- TypeTheory.Judgment

-- Terms (150 - 100)

infixl 150 _∘_ -- Foundation.Type.Transport
infixl 150 _∘_ -- Foundation.Function

infixl 140 _*_ -- Foundation.Data.Nat
infixl 130 _+_ -- Foundation.Data.Nat
infixl 130 _∙_ -- Foundation.Structure.Semigroup
infixl 120 _⊓_ -- Foundation.Data.Nat
infixl 120 _⊔_ -- Foundation.Data.Nat

infixr 100 _$_ -- Foundation.Function

-- Types (60 - 50)

infix 57 _×_ -- Foundation.Type.Sum
infix 55 _+_ -- Foundation.Type.Sum
infix 51 _,_ -- Foundation.Type.Sum
infix 50 _⟺_ -- Foundation.Type.Transport
infix 50 _,_ -- Foundation.Type.Transport

-- Logic formers (40 - 30)

infix 36 _⇝β_ _⇝v_ _⇝_ _↠_ -- TypeTheory.Computation
infix 36 _~_ -- TypeTheory.Confluence
infix 36 _▷_ -- TypeTheory.ParallelReduction

infix 35 _<_ -- Foundation.Data.Nat.Order
infix 35 _≤_ -- Foundation.Data.Nat.Order
infix 35 _<ₜ_ -- Foundation.Data.Nat.Order
infix 35 _<ₛ_ -- Foundation.Data.FinNat.Order
infix 35 _≤ₛ_ -- Foundation.Data.FinNat.Order

infix 21 _≤ₛ_ -- Foundation.Data.Relation.Property

-- Descriptive properties (20)

infix 20 _is-left-unit-of_ -- Foundation.Operation.Binary
infix 20 _is-right-unit-of_ -- Foundation.Operation.Binary
infix 20 _is-unit-of_ -- Foundation.Operation.Binary

-- Equalities (19)

infix 19 _==_ -- Foundation.Prop'.Identity.Definition
infix 19 _≠_ -- Foundation.Prop'.Identity
infix 19 _~_ -- Foundation.Function.Equivalence
infix 19 _~_ -- Foundation.Relation.Equivalence

-- Logic (18 - 10)

infix 18 ¬_ -- Foundation.Prop'.Empty
infixl 17 _∧_ -- Foundation.Prop'.Sum
infixl 15 _∨_ -- Foundation.Prop'.BinarySum
infix 11 _↔_ -- Foundation.Logic
infixl 11 _,_ -- Foundation.Prop'.Sum
infix 11 _,_ -- Foundation.Prop'.Sum
infix 11 _,_ -- Foundation.Prop'.Sum
infixl 11 _,_ -- Foundation.Logic
infix 11 _,_ -- Foundation.Operation.Property

-- Proof (10 - 5)

infix 7 proof_ -- Foundation.Proof
infix 5 _qed -- Foundation.Proof
infixl 6 _〉_〉_:by:_ -- Foundation.Proof

infix 4 have_:from:_ -- Foundation.Prop'.Proof
infixl 3 _⟶_:by:_ -- Foundation.Prop'.Proof

-- Universes (separate)

infix 1 _˙ -- Foundation.Universes
infix 1 _ᵖ -- Foundation.PropUniverses
