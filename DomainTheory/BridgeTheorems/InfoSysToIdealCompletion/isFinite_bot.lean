module
public import DomainTheory.InformationSystems.ElementsOfASystem.botElement
public import DomainTheory.InformationSystems.ElementsOfASystem.closure
import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.botElement_eq_closure_empty

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem isFinite_bot :
    ∃ (u : Finset α) (hu : u ∈ A.Con), A.botElement = A.closure u hu :=
  ⟨∅, A.con_empty, InfoSys.botElement.eq_closure_empty A⟩

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
