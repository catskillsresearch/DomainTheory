module
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.basicOpen

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

namespace InfoSysToNeighborhood

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem basicOpen_empty : A.basicOpen (∅ : Finset α) = (Set.univ : Set A.Element) := by
  ext x
  constructor
  · intro; trivial
  · intro _ a ha
    exact False.elim (Finset.notMem_empty a (Finset.mem_coe.1 ha))

end InfoSysToNeighborhood

end DomainTheory.BridgeTheorems
