/-ai
Tagging the cone of a finite binary string by a boolean yields the cone of that boolean followed by the string.

The tagging is the prepend of the one-bit list, and prepending that bit to a cone is the cone of the longer prefix.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.mem_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit_eq_prepend

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

/-- `b(σΣ*) = (bσ)Σ*`: prepending a bit to a cone gives the cone of the longer prefix. -/
theorem embBit_cone (b : Bool) (σ : Str) : embBit b (cone σ) = cone (b :: σ) := by
  rw [embBit_eq_prepend, prepend_cone]; rfl

end Example62

end DomainTheory.NeighbourhoodSystems
