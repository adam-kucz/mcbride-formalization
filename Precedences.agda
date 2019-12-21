module Precedences where

-- Terms (200 - 100)

infixl 150 _∘_ -- Foundation.Function.Equivalence

infixl 140 _*_ -- Foundation.Data.Nat
infixl 130 _+_ -- Foundation.Data.Nat

infixr 100 _$_ -- Foundation.Function.Equivalence

-- Types (60 - 50)

infix 55 _,_ -- Foundation.Type.Sum
infix 50 _×_ -- Foundation.Type.Sum

-- Logic formers (40 - 30)

infix 35 _<_ -- Foundation.Data.Nat.Order
infix 35 _≤_ -- Foundation.Data.Nat.Order
infix 35 _<ₜ_ -- Foundation.Data.Nat.Order

-- Descriptive properties (20)

infix 20 _is-left-unit-of_ -- Foundation.Operation.Binary
infix 20 _is-right-unit-of_ -- Foundation.Operation.Binary
infix 20 _is-unit-of_ -- Foundation.Operation.Binary

-- Equalities (19)

infix 19 _==_ -- Foundation.Prop'.Identity.Definition
infix 19 _≠_ -- Foundation.Prop'.Identity
infix 19 _~_ -- Foundation.Function.Equivalence

-- Logic (18 - 10)

infix 18 ¬_ -- Foundation.Prop'.Empty
infixl 17 _∧_ -- Foundation.Prop'.Sum
infixl 15 _∨_ -- Foundation.Prop'.BinarySum
infix 11 _↔_ -- Foundation.Logic
infix 11 _,_ -- Foundation.Prop'.Sum
infix 11 _,_ -- Foundation.Prop'.Sum
infix 11 _,_ -- Foundation.Prop'.Sum
infix 11 _,_ -- Foundation.Logic

-- Proof (10 - 5)

infix 7 proof_ -- Foundation.Proof
infix 5 _qed -- Foundation.Proof
infixl 6 _〉_〉_:by:_ -- Foundation.Proof

infix 4 have_:from:_ -- Foundation.Prop'.Proof
infixl 3 _⟶_:by:_ -- Foundation.Prop'.Proof

-- Universes (separate)

infix 1 _˙ -- Foundation.Universes
infix 1 _ᵖ -- Foundation.PropUniverses
