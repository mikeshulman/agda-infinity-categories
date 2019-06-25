{-# OPTIONS --no-eta-equality --without-K #-}

module Prelude.Size where

open import Agda.Builtin.Size public
  renaming (SizeU to U)
  renaming (Size<_ to <_)
  renaming (_⊔ˢ_ to _⊔_)
