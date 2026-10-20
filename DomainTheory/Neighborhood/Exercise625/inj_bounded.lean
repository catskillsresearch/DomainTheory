/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Proposition612
public import DomainTheory.Neighborhood.Exercise625.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Subsystem

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair








/-- **Exercise 6.25 — `g` maps consistent sets to consistent sets.** "Consistent" for sets of
elements is "bounded" (Exercise 1.27). If `S` is bounded by `b`, its image `{g(s) ∣ s ∈ S}` is
bounded by `g(b)` (monotonicity). -/
theorem inj_bounded (P : ProjectionPair D E) {S : Set D.Element} (hS : D.Bounded S) :
    E.Bounded (P.inj.toElementMap '' S) := by
  obtain ⟨b, hb⟩ := hS
  refine ⟨P.inj.toElementMap b, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  exact P.inj.toElementMap_mono (hb s hs)

end Subsystem.ProjectionPair
end DomainTheory.Neighborhood
