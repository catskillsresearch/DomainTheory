module
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.basicOpen
public import DomainTheory.InformationSystems.InformationSystems.Constructive.funion

@[expose] public section

namespace DomainTheory.BridgeTheorems


open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

namespace InfoSysToNeighborhood

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem basicOpen_singleton_inter (a : α) (s : Finset α) :
    A.basicOpen ({a} : Finset α) ∩ A.basicOpen s = A.basicOpen (insert a s) := by
  rw [basicOpen.inter A, funion.singleton_eq_insert]

end InfoSysToNeighborhood

end DomainTheory.BridgeTheorems
