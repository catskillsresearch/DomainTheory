module

public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.FiniteElement
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.finiteApproximants

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

def finiteApproximants (x : A.Element) : Set (FiniteElement A) :=
  { y | (y : A.Element) ∈ A.finiteApproximants x }

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
