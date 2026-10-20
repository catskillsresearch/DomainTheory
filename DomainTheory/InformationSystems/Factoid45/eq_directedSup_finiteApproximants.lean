/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Factoid36
import DomainTheory.InformationSystems.Factoid44
import DomainTheory.InformationSystems.Factoid45.Basic
import DomainTheory.InformationSystems.Factoid45.nonempty_finiteApproximants
import DomainTheory.InformationSystems.Factoid45.directed_finiteApproximants


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


/-- **Factoid 4.5 / algebraicity.** `x` is the directed lub of its finite approximants. -/
theorem eq_directedSup_finiteApproximants (x : sys.Element) :
    x = sys.directedSup (sys.finiteApproximants x)
      (sys.nonempty_finiteApproximants x) (sys.directed_finiteApproximants x) := by
  refine le_antisymm ?_ ?_
  · -- x ≤ directedSup: every token of x lies in some ū ⊆ x
    intro a ha
    have : a ∈ sys.approxUnion x := (sys.mem_element_iff_mem_closure x a).1 ha
    obtain ⟨u, hu, huX, ha'⟩ := this
    rw [sys.directedSup_carrier_eq_union]
    exact ⟨sys.closure u hu, ⟨u, hu, huX, rfl⟩, ha'⟩
  · -- directedSup ≤ x: each approximant is ≤ x
    apply sys.directedSup_le
    intro y hy
    obtain ⟨u, hu, huX, rfl⟩ := hy
    exact sys.closure_le_element x hu huX

end InfoSys
end DomainTheory.InformationSystems
