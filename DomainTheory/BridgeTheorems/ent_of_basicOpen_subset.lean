module
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.basicOpen
public import DomainTheory.InformationSystems.ElementsOfASystem.closure

@[expose] public section

namespace DomainTheory.BridgeTheorems


open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

namespace InfoSysToNeighborhood

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem ent_of_basicOpen_subset {u w : Finset α} (hw : w ∈ A.Con)
    (hsub : A.basicOpen w ⊆ A.basicOpen u) {a : α} (ha : a ∈ u) : A.Ent w a := by
  have : A.closure w hw ∈ A.basicOpen w := closure.subset A hw
  have hU : A.closure w hw ∈ A.basicOpen u := hsub this
  exact hU (Finset.mem_coe.2 ha)

end InfoSysToNeighborhood

end DomainTheory.BridgeTheorems
