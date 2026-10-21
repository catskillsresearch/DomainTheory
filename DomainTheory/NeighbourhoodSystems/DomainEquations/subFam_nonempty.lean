/-ai
The family of subdomain neighbourhood-sets of E is nonempty.

E is a subsystem of itself, so the collection of its own neighbourhoods belongs to the family.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Proposition611

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

variable {α : Type*}

/-- `subFam E` is non-empty: `E` itself is a subsystem (`Subsystem.refl`), so its own
neighbourhood-set `{X ∣ E.mem X}` is a member. -/
theorem subFam_nonempty (E : NeighborhoodSystem α) : (subFam E).Nonempty :=
  ⟨{X | E.mem X}, E, Subsystem.refl E, rfl⟩

end DomainTheory.NeighbourhoodSystems.Proposition611
