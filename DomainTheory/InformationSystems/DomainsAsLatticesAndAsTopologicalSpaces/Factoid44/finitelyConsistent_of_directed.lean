module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.IsDirected
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.exists_mem_of_subset_directedUnion

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- Directed families are finitely consistent on their carrier union. -/
theorem finitelyConsistent_of_directed (S : Set sys.Element) (hne : S.Nonempty)
    (hdir : sys.IsDirected S) :
    sys.IsFinitelyConsistent (sys.familyUnionCarrier S) := by
  intro Y hY
  obtain ⟨z, _hz, hYZ⟩ := sys.exists_mem_of_subset_directedUnion S hne hdir Y hY
  exact z.consistent Y hYZ

end InfoSys

end DomainTheory.InformationSystems
