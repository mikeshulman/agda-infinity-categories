{-# OPTIONS --no-eta-equality --without-K #-}

module Prelude where

module ∞ℕ where
  open import Prelude.Conatural public
open ∞ℕ public
  hiding (module ∞ℕ)

module ℕ where
  open import Prelude.Natural public
open ℕ public
  hiding (module ℕ)

module 𝕊 where
  open import Prelude.Preset public
open 𝕊 public
  using (Σ)
  using (tt)
  using (_,_)

module ∞Graph where
  open import Prelude.InfinityGraph public
open ∞Graph public
  hiding (module ∞Graph)
  using (∞Graph)
  using (*)
  using (∂)
  using (∞Map)
  using (ap)
  using (⇑_)

module Level where
  open import Prelude.Level public
open Level public
  using (Level)
  using (lz)
  using (ls)

open import Prelude.Path public

module Size where
  open import Prelude.Size public
open Size public
  hiding (∞)
