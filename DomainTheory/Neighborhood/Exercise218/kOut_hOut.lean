/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Example24
public import DomainTheory.Neighborhood.ApproximableExercises
public import DomainTheory.Neighborhood.Exercise218.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise218

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB ApproximableMap









/-- **`k` inverts `h` on prefixes.** `kOut (hOut σ) = σ`. -/
theorem kOut_hOut (σ : Str) : kOut (hOut σ) = σ := by
  induction σ with
  | nil => rfl
  | cons b t ih => simp only [hOut_cons, kOut_cons, ih]

end DomainTheory.Neighborhood.Exercise218
