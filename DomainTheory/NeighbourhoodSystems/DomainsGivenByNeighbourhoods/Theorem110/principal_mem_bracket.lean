/-ai
The principal filter of a neighbourhood belongs to the bracket of that neighbourhood.

The principal filter contains the neighbourhood by reflexivity of inclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.bracket
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.mem_bracket
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.bracket_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Theorem 1.10 (4).** `↑X ∈ [X]`: the principal filter of `X` contains `X`. -/
theorem principal_mem_bracket {X : Set α} (hX : V.mem X) : V.principal hX ∈ V.bracket X :=
  ⟨hX, subset_rfl⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
