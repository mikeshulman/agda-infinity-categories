{-# OPTIONS --no-eta-equality --without-K #-}
module Prelude.Preset where

private
  module Level where
    open import Prelude.Level public
  open Level
    using (Level)
    using (lz)
    using (ls)
    using (_⊔_)

infixr 0 _⇒_
_⇒_ : ∀ {i j} → Set i → Set j → Set (i ⊔ j)
A ⇒ B = A → B

idn : ∀ {i}{A : Set i} → A ⇒ A
idn x = x

seq : ∀ {i j k}{A : Set i}{B : Set j}{C : Set k} → A ⇒ B → B ⇒ C → A ⇒ C
seq f g x = g (f x)

data 𝟘 {i} : Set i where

¡ : ∀ {i j}{A : Set j} → 𝟘 {i} ⇒ A
¡ ()

record 𝟙 {i} : Set i where
  instance constructor tt

! : ∀ {i j}{A : Set i} → A ⇒ 𝟙 {j}
! _ = tt

module _×_ where
  open import Agda.Builtin.Sigma public
    using (Σ)
    using (_,_)
    using (fst)
    using (snd)
  open import Agda.Builtin.Sigma
  _×_ : ∀ {i j} → Set i → Set j → Set (i ⊔ j)
  A × B = Σ A λ _ → B
open _×_ public

⟨_,_⟩ : ∀ {i j k}{X : Set i}{A : Set j}{B : Set k} → X ⇒ A → X ⇒ B → X ⇒ A × B
⟨_,_⟩ F G x .fst = F x
⟨_,_⟩ F G x .snd = G x

⟨_×_⟩ : ∀ {i j k h}{X : Set i}{Y : Set j}{A : Set k}{B : Set h} → X ⇒ A → Y ⇒ B → X × Y ⇒ A × B
⟨_×_⟩ F G = ⟨ seq fst F , seq snd G ⟩

xchg : ∀ {i j k h}{A : Set i}{B : Set j}{C : Set k}{D : Set h} → (A × B) × (C × D) ⇒ (A × C) × (B × D)
xchg = ⟨ ⟨ fst × fst ⟩ , ⟨ snd × snd ⟩ ⟩
