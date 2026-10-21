/-ai
U's master neighbourhood, the half-open unit interval, is nonempty.

Zero belongs to it.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g1a.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `hD₀mne` for `U`: the master neighbourhood `U.master = Set.Ico 0 1` is non-empty. -/
theorem U_master_nonempty : U.master.Nonempty := ⟨0, by norm_num [U]⟩

end DomainTheory.NeighbourhoodSystems
