module

public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.finiteApproximants
import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.closure_le_element

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
