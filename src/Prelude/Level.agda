{-# OPTIONS --no-eta-equality --without-K #-}

module Prelude.Level where
  open import Agda.Primitive as Prim public
    using (_⊔_)
    using (Level)
    using (Setω)
    renaming (lsuc to ls)
    renaming (lzero to lz)

  record Lift {a} ℓ (A : Set a) : Set (a ⊔ ℓ) where
    constructor lift
    field
      lower : A
  open Lift public
