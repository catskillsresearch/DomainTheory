/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition87
import DomainTheory.Neighborhood.Theorem85
import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Nat.Bitwise
import Mathlib.Combinatorics.Colex
import DomainTheory.Neighborhood.Exercise812.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem




theorem affine_nonempty {k ℓ : ℕ} (hℓ : ℓ < 2 ^ k) : (affine k ℓ).Nonempty :=
  ⟨ℓ, Nat.mod_eq_of_lt hℓ⟩

end DomainTheory.Neighborhood
