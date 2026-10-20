/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic


namespace DomainTheory.DataTypesAsLattices































theorem squarePair_mono {x x' y y' : Pomega} (hx : x ⊆ x') (hy : y ⊆ y') :
    squarePair x y ⊆ squarePair x' y' := by
  intro k hk
  rcases hk with ⟨n, hn, hk⟩ | ⟨m, hm, hk⟩
  · exact Or.inl ⟨n, hx hn, hk⟩
  · exact Or.inr ⟨m, hy hm, hk⟩

end DomainTheory.DataTypesAsLattices
