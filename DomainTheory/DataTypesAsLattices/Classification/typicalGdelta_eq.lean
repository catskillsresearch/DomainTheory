/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import Mathlib.Data.Set.Finite.Powerset
import DomainTheory.DataTypesAsLattices.Classification.Basic


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace








































































































/-- **Scott 1976, Table 3.** `{⊤}` is a `Gδ`. -/
theorem typicalGdelta_eq : typicalGdelta = ⋂ n, {x : Pomega | n ∈ x} := by
  ext x
  constructor
  · intro hx
    refine Set.mem_iInter.mpr fun n => ?_
    have hx' : x = topElem := hx
    simp [hx']
  · intro hx
    ext k
    constructor
    · intro _; trivial
    · intro _
      exact Set.mem_iInter.mp hx k

end DomainTheory.DataTypesAsLattices
