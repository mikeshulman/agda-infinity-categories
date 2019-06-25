{-# OPTIONS --no-eta-equality --without-K #-}
module Prelude.Conatural where

private
  module ℕ where
    open import Prelude.Natural public
  open ℕ
    hiding (module ℕ)

  module 𝕊 where
    open import Prelude.Preset public
  open 𝕊
    using (Σ)
    using (tt)
    using (_,_)

infix 0 _≼_

mutual
  data ∞ℕ : Set where
    zero : ∞ℕ
    succ : [∞ℕ] → ∞ℕ

  record [∞ℕ] : Set where
    coinductive
    field
      force : ∞ℕ
open [∞ℕ] public

∞ : ∞ℕ
∞ = succ λ{ .force → ∞ }

into : ℕ → ∞ℕ
into zero = zero
into (succ n) = succ λ{ .force → into n }

module _ where
  open import Agda.Builtin.FromNat
  open Number
  instance
    ∞nat : Number ∞ℕ
    ∞nat .Constraint n = 𝕊.𝟙
    ∞nat .fromNat n ⦃ tt ⦄ = into n

_≼_ : ℕ → ∞ℕ → Set
zero ≼ n = 𝕊.𝟙
succ m ≼ zero = 𝕊.𝟘
succ m ≼ succ n = m ≼ force n

↑≼ : ∀ {m n} .(p : m ≼ force n) → m ≼ succ n
↑≼ {zero} {n} p = tt
↑≼ {succ m} {n} p with force n
↑≼ {succ m} {n} () | zero
↑≼ {succ m} {n} p  | succ n′ = ↑≼ {m} {n′} p

↓≼ : ∀ {m} (n : ∞ℕ) .(p : succ m ≼ n) → m ≼ n
↓≼ {zero} n p = tt
↓≼ {succ m} zero ()
↓≼ {succ m} (succ n) p = ↓≼ (force n) p
