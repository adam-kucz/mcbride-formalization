{-# OPTIONS --prop  #-}
module Unit where

open import Univ
  using (𝑙)

record Unit : Set 𝑙 where
  instance
    constructor unit

private
  variable l : Unit


