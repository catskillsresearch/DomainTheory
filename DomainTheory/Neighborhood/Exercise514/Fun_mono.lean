/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise513
import Mathlib.Data.List.Basic
import DomainTheory.Neighborhood.Exercise514.Basic


namespace DomainTheory.Neighborhood.Exercise514

open DomainTheory.Neighborhood.Exercise513












/-- **`Fun` is monotone in both arguments jointly.** Needed to check the `mono` axiom of the
neighbourhood-level approximable map built from `Fun` (Exercise 7.23). -/
theorem Fun_mono {u u' x x' : Set ℕ} (hu : u ⊆ u') (hx : x ⊆ x') : Fun u x ⊆ Fun u' x' := by
  rintro m ⟨ns, hns, htag⟩
  exact ⟨ns, fun n hn => hx (hns n hn), hu htag⟩

end DomainTheory.Neighborhood.Exercise514
