{-# OPTIONS --no-eta-equality --without-K #-}
module Prelude.Natural where

private
  module 𝕊 where
    open import Prelude.Preset public
  open 𝕊
    using (Σ)
    using (tt)
    using (_,_)

open import Agda.Builtin.Nat public
  renaming (Nat to ℕ)
  renaming (suc to succ)
open import Agda.Builtin.FromNat
open Number
instance
  nat : Number ℕ
  nat .Constraint _ = 𝕊.𝟙
  nat .fromNat n = n
