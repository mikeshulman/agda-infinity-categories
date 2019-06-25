
{-# OPTIONS --no-eta-equality --without-K #-}
module Prelude.InfinityGraph where

private
  module 𝕊 where
    open import Prelude.Preset public
  open 𝕊
    using (Σ)
    using (tt)
    using (_,_)

  module Level where
    open import Prelude.Level public
  open Level
    using (Level)
    using (lz)
    using (ls)
    using (_⊔_)

  module Size where
    open import Prelude.Size public
  open Size
    hiding (∞)
    hiding (_⊔_)

record ∞Graph {s : Size} {i : Level} : Set (ls i) where
  coinductive
  field
    * : Set i
    ∂ : (x y : *) {s′ : Size.< s} → ∞Graph {s′} {i}
open ∞Graph public

record ∞Map {s} {i j : Level} (A : ∞Graph {s} {i}) (B : ∞Graph {s} {j}) : Set (i ⊔ j) where
  coinductive
  infixr 0 ⇑_
  field
    ap : * A → * B
    ⇑_ : ∀ {x y} {s′ : Size.< s} → ∞Map {s′} (A .∂ x y) (B .∂ (ap x) (ap y))
open ∞Map public

idn : ∀ {s i A} → ∞Map {s}{i} A A
idn .ap = 𝕊.idn
idn .⇑_ = idn

seq : ∀ {s i j k A B C} → ∞Map {s}{i}{j} A B → ∞Map {s}{j}{k} B C → ∞Map {s}{i}{k} A C
seq F G .ap = 𝕊.seq (ap F) (ap G)
seq F G .⇑_ = seq (⇑ F) (⇑ G)

𝟘 : ∀ {s i} → ∞Graph {s}{i}
𝟘 .* = 𝕊.𝟘
𝟘 .∂ () ()

¡ : ∀ {s i j A} → ∞Map {s}{i}{j} 𝟘 A
¡ .ap = 𝕊.¡
¡ .⇑_ {()}{()}

𝟙 : ∀ {s i} → ∞Graph {s}{i}
𝟙 .* = 𝕊.𝟙
𝟙 .∂ x y = 𝟙

! : ∀ {s i j A} → ∞Map {s}{i}{j} A 𝟙
! .ap = 𝕊.!
! .⇑_ = !

_×_ : ∀ {s i j} → ∞Graph {s}{i} → ∞Graph {s}{j} → ∞Graph {s}{i ⊔ j}
_×_ A B .* = * A 𝕊.× * B
_×_ A B .∂ (a₀ , b₀) (a₁ , b₁) = A .∂ a₀ a₁ × B .∂ b₀ b₁

fst : ∀ {s i j}{A : ∞Graph {s}{i}}{B : ∞Graph {s}{j}} → ∞Map (A × B) A
fst .ap = 𝕊.fst
fst .⇑_ = fst

snd : ∀ {s i j}{A : ∞Graph {s}{i}}{B : ∞Graph {s}{j}} → ∞Map (A × B) B
snd .ap = 𝕊.snd
snd .⇑_ = snd

⟨_,_⟩ : ∀ {s i j k X A B} → ∞Map {s}{i}{j} X A → ∞Map {s}{i}{k} X B → ∞Map {s}{i}{j ⊔ k} X (A × B)
⟨_,_⟩ F G .ap = 𝕊.⟨ ap F , ap G ⟩
⟨_,_⟩ F G .⇑_ = ⟨ ⇑ F , ⇑ G ⟩

⟨_×_⟩ : ∀ {s i j m n X Y A B} → ∞Map {s}{i}{m} X A → ∞Map {s}{j}{n} Y B → ∞Map {s}{i ⊔ j}{m ⊔ n} (X × Y) (A × B)
⟨_×_⟩ F G = ⟨ seq fst F , seq snd G ⟩

xchg : ∀ {s i j m n}{A : ∞Graph {s}{i}}{B : ∞Graph {s}{j}}{C : ∞Graph {s}{m}}{D : ∞Graph {s}{n}} → ∞Map {s} ((A × B) × (C × D)) ((A × C) × (B × D))
xchg = ⟨ ⟨ fst × fst ⟩ , ⟨ snd × snd ⟩ ⟩
