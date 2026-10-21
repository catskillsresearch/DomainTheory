/-ai
For neighbourhoods X and Y, the bracket of X is contained in the bracket of Y if and only if X is contained in Y.

If the brackets are nested, the principal filter of X lies in the bracket of X and hence in the bracket of Y, and the inclusion is the second component of that membership. Conversely, if X is contained in Y, an element containing X contains Y by upward closure.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.bracket
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.mem_bracket
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.bracket_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.principal_mem_bracket

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **The correspondence `X ↦ [X]` is inclusion-preserving.** `[X] ⊆ [Y] ↔ X ⊆ Y` (for `X,Y ∈ 𝒟`).
`→` tests at `↑X ∈ [X]`, reading `X ⊆ Y` off `↑X ∈ [Y]`; `←` is upward closure. -/
theorem bracket_subset_iff {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    V.bracket X ⊆ V.bracket Y ↔ X ⊆ Y := by
  constructor
  · intro h
    exact (h (V.principal_mem_bracket hX)).2
  · intro hXY x hx
    exact x.up_mem hx hY hXY

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
