/-ai
The cone of the empty string is the set of all finite binary strings.

Compare the two sets by extensionality and simplify the definition of a cone.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.List.Infix
import all Mathlib.Data.List.Infix
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.cone
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.mem_cone

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- `ΛΣ* = Σ*`: the cone of the empty string is everything (Scott's `Δ`). -/
theorem cone_nil : cone [] = Set.univ := by
  ext w; simp [cone]

end DomainTheory.NeighbourhoodSystems.ExampleB
