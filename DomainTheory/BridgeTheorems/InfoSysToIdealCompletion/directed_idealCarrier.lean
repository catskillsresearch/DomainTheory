/-ai
The set of underlying elements of an ideal of finite elements is directed.

Two members of the carrier come from finite elements of the ideal. The ideal is directed, so those finite elements lie under a third finite element of the ideal, whose underlying element is a common upper bound in the carrier.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Ideal
import all Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.FiniteElement
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.idealCarrier

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem directed_idealCarrier (I : Ideal (FiniteElement A)) :
    A.IsDirected (idealCarrier A I) := by
  intro x y hx hy
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  obtain ⟨z', hz', hxz, hyz⟩ := I.directed x' hx' y' hy'
  exact ⟨z', ⟨z', hz', rfl⟩, hxz, hyz⟩

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
