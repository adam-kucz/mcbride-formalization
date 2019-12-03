{-# OPTIONS --prop  #-}
module Foundations.Functions.Extensionality where

open import Foundations.Univ using (𝑙; 𝑚)
open import Foundations.Equality.Core using (_==_)

postulate
  fun-ext :
    {A : Set 𝑙}
    {B B' : A → Set 𝑚}
    {f : (x : A) → B x}
    {f' : (x : A) → B' x}
    (ext : (x : A) → f x == f' x)
    → ----------------------
    f == f'
    
