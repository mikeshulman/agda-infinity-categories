{-# OPTIONS --no-eta-equality --without-K #-}

module InfinityCategory where

open import Prelude

module _ {i} (Θ : ∞Graph {Size.∞} {i}) where
  infix 0 _∈_
  infixl 6 _▸_⇒_

  -- An inductive-recursive universe of globular sets; these provide inductive,
  -- telescopic representations of globular boundaries from some underlying hom
  -- ∞Graph, i.e., `Θ .∂ x y .∂ f g` is represented as `· ▸ x ⇒ y ▸ f ⇒ g`.
  mutual
    data Glob : Set i where
      · : Glob
      _▸_⇒_ : (Γ : Glob) (x y : ⟦Glob⟧ Γ .*) → Glob

    ⟦Glob⟧ : Glob → ∞Graph {Size.∞}{i}
    ⟦Glob⟧ · = Θ
    ⟦Glob⟧ (Γ ▸ x ⇒ y) = ⟦Glob⟧ Γ .∂ x y

  -- An inductive-recursive universe of (biased) "pasting diagrams" (FIXME);
  -- diagrams differ from globs in that each subsequent dimension can be
  -- comprised of formal operations (identity, composition, etc.) of formal
  -- cells from the previous dimension.
  mutual
    data Diagram : Set i where
      · : Diagram
      _▸_⇒_ : (Ψ : Diagram) (x y : ⟦Diagram⟧ Ψ) → Diagram

    ⟦Diagram⟧ : Diagram → Set i
    ⟦Diagram⟧ · = * Θ
    ⟦Diagram⟧ (Ψ ▸ x ⇒ y) = Cell (Ψ ▸ x ⇒ y)

    -- Atoms allow us to embed edges from the underlying hom ∞Graph into cells
    record Atom (Ψ : Diagram) : Set i where
      inductive
      constructor [_⊢_]
      field
        {Γ} : Glob
        coe : Ψ ∈ Γ
        elm : ⟦Glob⟧ Γ .*
    pattern [_] {Γ}{coe} elm = [_⊢_] {Γ} coe elm

    -- Cells indexed on diagrams. This isn't quite a monad but we don't seem to need that (FIXME).
    data Cell : Diagram → Set i where
      -- embeds an atom into a cell
      atom : ∀ {Ψ} → Atom Ψ → Cell Ψ
      -- identity
      idn : ∀ {Ψ x} → Cell (Ψ ▸ x ⇒ x)
      -- composition; diagrammatic order
      seq : ∀ {Ψ x y z} (f : Cell (Ψ ▸ x ⇒ y)) (g : Cell (Ψ ▸ y ⇒ z)) → Cell (Ψ ▸ x ⇒ z)
      -- composition functoriality
      seq* : ∀ {Ψ x y z f f′ g g′}(α : Cell (Ψ ▸ x ⇒ y ▸ f ⇒ f′))(β : Cell (Ψ ▸ y ⇒ z ▸ g ⇒ g′)) → Cell (Ψ ▸ x ⇒ z ▸ seq {y = y} f g ⇒ seq {y = y} f′ g′)
      -- inverse
      inv : ∀ {Ψ x y f g} (α : Cell (Ψ ▸ x ⇒ y ▸ g ⇒ f)) → Cell (Ψ ▸ x ⇒ y ▸ f ⇒ g)
      -- inverse functoriality
      inv* : ∀ {Ψ x y f g α β} (𝔭 : Cell (Ψ ▸ x ⇒ y ▸ f ⇒ g ▸ β ⇒ α)) → Cell (Ψ ▸ x ⇒ y ▸ g ⇒ f ▸ inv α ⇒ inv β)
      -- left identity
      mon-λ : ∀ {Ψ x y f} → Cell (Ψ ▸ x ⇒ y ▸ seq idn f ⇒ f)
      -- right identity
      mon-ρ : ∀ {Ψ x y f} → Cell (Ψ ▸ x ⇒ y ▸ seq f idn ⇒ f)
      -- associativity
      mon-α : ∀ {Ψ w x y z f h}{g : Cell (Ψ ▸ x ⇒ y)} → Cell (Ψ ▸ w ⇒ z ▸ seq (seq f g) h ⇒ seq f (seq g h))
      gpd-ι : ∀ {Ψ x y f g}{α : Cell (Ψ ▸ x ⇒ y ▸ f ⇒ g)} → Cell (Ψ ▸ x ⇒ y ▸ g ⇒ g ▸ seq (inv α) α ⇒ idn)
      gpd-κ : ∀ {Ψ x y f g}{α : Cell (Ψ ▸ x ⇒ y ▸ f ⇒ g)} → Cell (Ψ ▸ x ⇒ y ▸ f ⇒ f ▸ seq α (inv α) ⇒ idn)
      -- coherence cell; if two cells are coherent (thin or hollow) and have the
      -- same "boundary", then a mediating coherence cell between them exists
      coh : ∀ {Ψ} {f g : ⟦Diagram⟧ Ψ} (ϕ : Thin Ψ f) (ψ : Thin Ψ g) → Cell (Ψ ▸ f ⇒ g)

    -- Evidence that a diagram Ψ can be represented as a globular set Γ
    data _∈_ : Diagram → Glob → Set i where
      z : ∀ {a b}
        → · ▸ a ⇒ b ∈ · ▸ a ⇒ b
      s_ : ∀ {Ψ a b Γ x y f g}
        → (ϕ : Ψ ▸ a ⇒ b ∈ Γ ▸ x ⇒ y)
        → Ψ ▸ a ⇒ b ▸ atom [ ϕ ⊢ f ] ⇒ atom [ ϕ ⊢ g ] ∈ Γ ▸ x ⇒ y ▸ f ⇒ g

    -- Coherence predicate on cells
    data Thin : ∀ Ψ → ⟦Diagram⟧ Ψ → Set i where
      idn : ∀ {Ψ x} → Thin (Ψ ▸ x ⇒ x) idn
      seq : ∀ {Ψ x y z f g} → Thin (Ψ ▸ x ⇒ y) f → Thin (Ψ ▸ y ⇒ z) g → Thin (Ψ ▸ x ⇒ z) (seq f g)
      seq* : ∀ {Ψ x y z f f′ g g′ α β} → Thin (Ψ ▸ x ⇒ z ▸ seq {y = y} f g ⇒ seq f′ g′) (seq* α β)
      mon-λ : ∀ {Ψ x y f} → Thin (Ψ ▸ x ⇒ y ▸ seq idn f ⇒ f) mon-λ
      mon-ρ : ∀ {Ψ x y f} → Thin (Ψ ▸ x ⇒ y ▸ seq f idn ⇒ f) mon-ρ
      mon-α : ∀ {Ψ w x y z f h}{g : Cell (Ψ ▸ x ⇒ y)} → Thin (Ψ ▸ w ⇒ z ▸ seq (seq f g) h ⇒ seq f (seq g h)) mon-α
      gpd-ι : ∀ {Ψ x y f g}{α : Cell (Ψ ▸ x ⇒ y ▸ f ⇒ g)} → Thin (Ψ ▸ x ⇒ y ▸ g ⇒ g ▸ seq (inv α) α ⇒ idn) gpd-ι
      gpd-κ : ∀ {Ψ x y f g}{α : Cell (Ψ ▸ x ⇒ y ▸ f ⇒ g)} → Thin (Ψ ▸ x ⇒ y ▸ f ⇒ f ▸ seq α (inv α) ⇒ idn) gpd-κ
      coh : ∀ {Ψ} {f g : ⟦Diagram⟧ Ψ} (ϕ : Thin Ψ f) (ψ : Thin Ψ g) → Thin (Ψ ▸ f ⇒ g) (coh ϕ ψ)

  dim : Diagram → ℕ
  dim · = zero
  dim (Ψ ▸ _ ⇒ _) = succ (dim Ψ)

  -- A cellular "prealgebra"; this consists of enough data to map cells into an
  -- ∞Graph in all dimensions, but we do not yet require that `fuse` and `fill`
  -- are well behaved.
  record PreAlg n
    (fuse : (Ψ : Diagram) .{ϕ : dim Ψ ≼ n} → Glob)
    (fill : (Ψ : Diagram) .{ϕ : dim Ψ ≼ n} → ⟦Diagram⟧ Ψ → ⟦Glob⟧ (fuse Ψ {ϕ}) .*)
    : Set i where
    ⟦Cell⟧ : ∀ (Ψ : Diagram) .{ϕ : dim Ψ ≼ n} (x y : ⟦Diagram⟧ Ψ) → Set i
    ⟦Cell⟧ Ψ {ϕ} x y = ⟦Glob⟧ (fuse Ψ {ϕ}) .∂ (fill Ψ x) (fill Ψ y) .*
    field
      ⟦atom⟧ : ∀ {Ψ}.{ϕ}{x y} → Atom (Ψ ▸ x ⇒ y) → ⟦Cell⟧ Ψ {ϕ} x y
      ⟦idn⟧ : ∀ {Ψ}.{ϕ}{x} → ⟦Cell⟧ Ψ {ϕ} x x
      ⟦seq⟧ : ∀ {Ψ}.{ϕ}{x y z} (f : ⟦Cell⟧ Ψ {ϕ} x y) (g : ⟦Cell⟧ Ψ {ϕ} y z) → ⟦Cell⟧ Ψ {ϕ} x z
      ⟦seq*⟧ : ∀ {Ψ}.{ϕ}{x y z f f′ g g′}(α : ⟦Cell⟧ (Ψ ▸ x ⇒ y) {ϕ} f f′)(β : ⟦Cell⟧ (Ψ ▸ y ⇒ z) {ϕ} g g′) → ⟦Cell⟧ (Ψ ▸ x ⇒ z) {ϕ} (seq {y = y} f g) (seq {y = y} f′ g′)
      ⟦inv⟧ : ∀ {Ψ}.{ϕ}{x y f g} → ⟦Cell⟧ (Ψ ▸ x ⇒ y) {ϕ} f g → ⟦Cell⟧ (Ψ ▸ x ⇒ y) {ϕ} g f
      ⟦inv*⟧ : ∀ {Ψ}.{ϕ}{x y f g}{α β : Cell (Ψ ▸ x ⇒ y ▸ g ⇒ f)}(𝔭 : ⟦Cell⟧ (Ψ ▸ x ⇒ y ▸ g ⇒ f) {ϕ} β α) → ⟦Cell⟧ (Ψ ▸ x ⇒ y ▸ f ⇒ g) {ϕ} (inv α) (inv β)
      ⟦mon-λ⟧ : ∀ {Ψ}.{ϕ}{x y f} → ⟦Cell⟧ (Ψ ▸ x ⇒ y) {ϕ} (seq idn f) f
      ⟦mon-ρ⟧ : ∀ {Ψ}.{ϕ}{x y f} → ⟦Cell⟧ (Ψ ▸ x ⇒ y) {ϕ} (seq f idn) f
      ⟦mon-α⟧ : ∀ {Ψ}.{ϕ}{w x y z f h}{g : Cell (Ψ ▸ x ⇒ y)} → ⟦Cell⟧ (Ψ ▸ w ⇒ z) {ϕ} (seq (seq f g) h) (seq f (seq g h))
      ⟦gpd-ι⟧ : ∀ {Ψ}.{ϕ}{x y f g α} → ⟦Cell⟧ (Ψ ▸ x ⇒ y ▸ g ⇒ g) {ϕ} (seq {y = f} (inv α) α) idn
      ⟦gpd-κ⟧ : ∀ {Ψ}.{ϕ}{x y f g α} → ⟦Cell⟧ (Ψ ▸ x ⇒ y ▸ f ⇒ f) {ϕ} (seq {y = g} α (inv α)) idn
      ⟦coh⟧ : ∀ {Ψ}.{ϕ}{f g : ⟦Diagram⟧ Ψ} (ψ₀ : Thin Ψ f) (ψ₁ : Thin Ψ g) → ⟦Cell⟧ Ψ {ϕ} f g
  open PreAlg public

  -- Given a cellular prealgebra and a formal cell, we can obtain a corresponding semantic edge
  fold : ∀ {n fuse fill} (𝔉 : PreAlg n fuse fill) → ∀ {Ψ x y} → Cell (Ψ ▸ x ⇒ y) → .{ϕ : dim Ψ ≼ n} → ⟦Cell⟧ 𝔉 Ψ {ϕ} x y
  fold 𝔉 (atom f) = ⟦atom⟧ 𝔉 f
  fold 𝔉 idn = ⟦idn⟧ 𝔉
  fold 𝔉 (seq f g) = ⟦seq⟧ 𝔉 (fold 𝔉 f) (fold 𝔉 g)
  fold 𝔉 (seq* f g) = ⟦seq*⟧ 𝔉 (fold 𝔉 f) (fold 𝔉 g)
  fold 𝔉 (inv f) = ⟦inv⟧ 𝔉 (fold 𝔉 f)
  fold 𝔉 (inv* α) = ⟦inv*⟧ 𝔉 (fold 𝔉 α)
  fold 𝔉 (mon-λ) = ⟦mon-λ⟧ 𝔉
  fold 𝔉 (mon-ρ) = ⟦mon-ρ⟧ 𝔉
  fold 𝔉 (mon-α) = ⟦mon-α⟧ 𝔉
  fold 𝔉 (gpd-ι) = ⟦gpd-ι⟧ 𝔉
  fold 𝔉 (gpd-κ) = ⟦gpd-κ⟧ 𝔉
  fold 𝔉 (coh ϕ ψ) = ⟦coh⟧ 𝔉 ϕ ψ

-- An n-category is ...
record Category (n : ∞ℕ) {i} : Set (ls i) where
  field
    -- an underlying hom ∞Graph
    hom : ∞Graph {Size.∞} {i}
  field
    -- with operations `fuse` and `fill` (completely determined by the equations in the next block)
    {fuse} : (Ψ : Diagram hom) .{ϕ : dim hom Ψ ≼ n} → Glob hom
    {fill} : (Ψ : Diagram hom) .{ϕ : dim hom Ψ ≼ n} → ⟦Diagram⟧ hom Ψ → ⟦Glob⟧ hom (fuse Ψ {ϕ}) .*
    -- and a cellular prealgebra
    pre : PreAlg hom n fuse fill
  field
    -- subject to the following "continuity" conditions; as a corollary, these
    -- ensure the algebra maps n-dimensional cells to n-dimensional edges
    ⦃fuse/nil⦄ : fuse · {tt} ≡ ·
    ⦃fuse/ext⦄ : ∀ {Ψ x y}.{ϕ : 1 + dim hom Ψ ≼ n} → fuse (Ψ ▸ x ⇒ y) {ϕ} ≡ fuse Ψ {↓≼ n ϕ} ▸ fill Ψ x ⇒ fill Ψ y
    ⦃fill/nil⦄ : ∀ {x} → fill · {tt} x ≅ x
    ⦃fill/ext⦄ : ∀ {Ψ x y f}.{ϕ : 1 + dim hom Ψ ≼ n} → fill (Ψ ▸ x ⇒ y) {ϕ} f ≅ fold hom pre f {↓≼ n ϕ}
open Category public
  hiding (hom)
  hiding (fuse)
  hiding (fill)
