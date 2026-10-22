module

public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.idealCarrier
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44.IsDirected
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

theorem directed_idealCarrier (I : Ideal (FiniteElement A)) :
    A.IsDirected (idealCarrier A I) := by
  intro x y hx hy
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  obtain ⟨z', hz', hxz, hyz⟩ := I.directed x' hx' y' hy'
  exact ⟨z', ⟨z', hz', rfl⟩, hxz, hyz⟩

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
