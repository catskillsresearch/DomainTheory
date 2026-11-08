module

public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.finiteApproximants
public import DomainTheory.InformationSystems.ElementsOfASystem.closure
public import DomainTheory.InformationSystems.InformationSystems.InfoSys.Element
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.factoid_45
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.FiniteElement

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem mem_finiteApproximants_of_le {x : A.Element} {y : FiniteElement A}
    (hle : (y : A.Element) ≤ x) : y ∈ finiteApproximants A x := by
  rcases y with ⟨yval, ⟨u, hu, rfl⟩⟩
  refine ⟨u, hu, ?_, rfl⟩
  intro a ha
  exact hle (closure.subset A hu ha)

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
