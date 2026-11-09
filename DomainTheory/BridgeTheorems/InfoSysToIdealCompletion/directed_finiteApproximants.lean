module

public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.finiteApproximants
public import Mathlib.Order.Directed
import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.closures_directed

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem directed_finiteApproximants (x : A.Element) :
    DirectedOn (· ≤ ·) (finiteApproximants A x) := by
  intro y₁ hy₁ y₂ hy₂
  obtain ⟨u, hu, huX, hy₁eq⟩ := hy₁
  obtain ⟨v, hv, hvX, hy₂eq⟩ := hy₂
  obtain ⟨w, hw, hwX, huw, hvw⟩ := A.closures_directed x hu hv huX hvX
  refine ⟨⟨A.closure w hw, ⟨w, hw, rfl⟩⟩, ⟨w, hw, hwX, rfl⟩, ?_, ?_⟩
  ·
    change (y₁ : A.Element) ≤ A.closure w hw
    exact hy₁eq ▸ huw
  · change (y₂ : A.Element) ≤ A.closure w hw
    exact hy₂eq ▸ hvw

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
