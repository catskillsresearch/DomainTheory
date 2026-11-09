module
public import DomainTheory.InformationSystems.ElementsOfASystem.closure

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

abbrev FiniteElement : Type _ :=
  { x : A.Element // ∃ (u : Finset α) (hu : u ∈ A.Con), x = A.closure u hu }

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
