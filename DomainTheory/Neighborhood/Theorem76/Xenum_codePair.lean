/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem75
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Theorem76.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}






variable (P : ComputablePresentation V)

/-- `Xenum (codePair a b) = [X_a, X_b]` (a one-entry, always-consistent function-space
neighbourhood); a thin wrapper around `Xenum_singleton`. -/
theorem Xenum_codePair (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P P (decodeList c))
      : Set (ApproximableMap V V)).Nonempty) (a b : ℕ) :
    Xenum P P gN (codePair a b) = step (P.X a) (P.X b) :=
  Xenum_singleton P P gN hgN a b

end DomainTheory.Neighborhood
