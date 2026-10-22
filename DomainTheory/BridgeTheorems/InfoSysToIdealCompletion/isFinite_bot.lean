module
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45.botElement_eq_closure_empty
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33.botElement
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35.closure
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45


@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem isFinite_bot :
    ∃ (u : Finset α) (hu : u ∈ A.Con), A.botElement = A.closure u hu :=
  ⟨∅, A.con_empty, A.botElement_eq_closure_empty⟩

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
