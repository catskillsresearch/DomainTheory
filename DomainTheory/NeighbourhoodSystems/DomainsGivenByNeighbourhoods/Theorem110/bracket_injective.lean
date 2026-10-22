module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.bracket
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.mem_bracket
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.bracket_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.bracket_subset_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **The correspondence `X ↦ [X]` is one-one.** `[X] = [Y] ⟹ X = Y` (for `X,Y ∈ 𝒟`). -/
theorem bracket_injective {X Y : Set α} (hX : V.mem X) (hY : V.mem Y)
    (h : V.bracket X = V.bracket Y) : X = Y :=
  Set.Subset.antisymm ((V.bracket_subset_iff hX hY).mp h.subset)
    ((V.bracket_subset_iff hY hX).mp h.superset)

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
