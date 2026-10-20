module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.IsChain
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.IsDirected_of_IsChain
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.directedSup

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- Chain unions are elements. -/
def chainSup (S : Set sys.Element) (hne : S.Nonempty) (hchain : sys.IsChain S) : sys.Element :=
  sys.directedSup S hne (sys.IsDirected_of_IsChain hchain)

end InfoSys

end DomainTheory.InformationSystems
