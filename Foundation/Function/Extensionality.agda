{-# OPTIONS --exact-split --prop  #-}
module Foundation.Function.Extensionality where

open import Foundation.Universes
open import Foundation.Prop'.Identity using (_==_)

postulate
  fun-ext :
    {f : (x : X) → A x}
    {f' : (x : X) → B x}
    (ext : (x : X) → f x == f' x)
    → ----------------------
    f == f'
    
