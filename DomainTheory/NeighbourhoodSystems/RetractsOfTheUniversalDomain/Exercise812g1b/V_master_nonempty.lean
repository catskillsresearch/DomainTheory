/-ai
V's master neighbourhood, the set of all natural numbers, is nonempty.

The universe is nonempty.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g1b.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `hD₁mne` for `V`: the master neighbourhood `V.master = Set.univ` is non-empty. -/
theorem V_master_nonempty : V.master.Nonempty := Set.univ_nonempty

end DomainTheory.NeighbourhoodSystems
