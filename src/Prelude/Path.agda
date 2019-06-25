{-# OPTIONS --no-eta-equality --type-in-type --without-K #-}

module Prelude.Path where

private
  module Level where
    open import Prelude.Level public
  open Level
    using (Level)
    using (lz)
    using (ls)
    using (_⊔_)

module ≡ where
  open import Agda.Builtin.Equality public
    renaming (refl to idn)

  seq : ∀ {i}{A : Set i} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  seq idn g = g

  inv : ∀ {i}{A : Set i} {x y : A} → x ≡ y → y ≡ x
  inv idn = idn
open ≡ public
  hiding (module _≡_)
  using (_≡_)

module ≅ where
  data _≅_ {i} {A : Set i} (x : A) : ∀ {j} {B : Set j} (y : B) → Set i where
    idn : x ≅ x

  -- seq : ∀ {i j k}{A : Set i}{B : Set j}{C : Set k}{x : A}{y : B}{z : C} → x ≅ y → y ≅ z → x ≅ z
  -- seq idn g = g

  -- inv : ∀ {i j}{A : Set i}{B : Set j}{x : A}{y : B} → x ≅ y → y ≅ x
  -- inv idn = idn
open ≅ public
  hiding (module _≅_)
  using (_≅_)
