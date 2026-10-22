module

public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.finiteApproximants
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.closure_le_element
public import DomainTheory.InformationSystems.InformationSystems.InfoSys.Basic
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.FiniteElement

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem le_of_mem_finiteApproximants {x : A.Element} {y : FiniteElement A}
    (hy : y ∈ finiteApproximants A x) : (y : A.Element) ≤ x := by
  obtain ⟨u, hu, huX, hyeq⟩ := hy
  exact hyeq ▸ A.closure_le_element x hu huX

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
