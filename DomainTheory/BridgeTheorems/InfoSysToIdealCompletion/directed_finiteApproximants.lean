/-ai
The finite approximants of an element x, viewed as finite elements, are directed.

Two finite approximants are closures of consistent finite sets of tokens of x. Directedness of closures supplies a consistent finite set of tokens of x whose closure lies above both closures, and that closure is a finite approximant above both.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.finiteApproximants

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
  · -- y₁ ≤ closure w
    change (y₁ : A.Element) ≤ A.closure w hw
    exact hy₁eq ▸ huw
  · change (y₂ : A.Element) ≤ A.closure w hw
    exact hy₂eq ▸ hvw

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
