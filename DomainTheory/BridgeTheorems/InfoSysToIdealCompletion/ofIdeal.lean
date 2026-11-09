module

public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.nonempty_idealCarrier
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.directed_idealCarrier
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.directedSup

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

noncomputable def ofIdeal (I : Ideal (FiniteElement A)) : A.Element :=
  A.directedSup (idealCarrier A I) (nonempty_idealCarrier A I) (directed_idealCarrier A I)

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
