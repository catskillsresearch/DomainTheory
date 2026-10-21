/-ai
Factoid 4.4 defines the supremum of a nonempty directed family of elements to be the join of the family, using that the union of the carriers of a nonempty directed family is finitely consistent.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.IsDirected
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.finitelyConsistent_of_directed

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- **Factoid 4.4.** Union of a nonempty directed family is an element (as `familySup`). -/
def directedSup (S : Set sys.Element) (hne : S.Nonempty) (hdir : sys.IsDirected S) :
    sys.Element :=
  sys.familySup S (sys.finitelyConsistent_of_directed S hne hdir)

end InfoSys

end DomainTheory.InformationSystems
