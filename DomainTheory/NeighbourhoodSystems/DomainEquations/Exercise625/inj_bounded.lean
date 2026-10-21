/-ai
The injection of a projection pair sends a bounded set of elements to a bounded set.

If an element bounds the set, its image bounds the image of the set, because the injection is monotone on elements.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

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
end DomainTheory.NeighbourhoodSystems
