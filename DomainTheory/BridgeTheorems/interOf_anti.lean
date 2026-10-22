module

public import DomainTheory.BridgeTheorems.interOf
public import DomainTheory.BridgeTheorems.mem_interOf
public import Mathlib.Data.Finset.Fold
public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.NbhdBasis
public import DomainTheory.BridgeTheorems.interOf_empty

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

/-- Larger index sets give smaller intersections. -/
theorem interOf_anti {u v : Finset ι} (h : u ⊆ v) : B.interOf v ⊆ B.interOf u := by
  intro x hx
  exact B.mem_interOf.mpr ⟨(B.mem_interOf.mp hx).1, fun i hi => (B.mem_interOf.mp hx).2 i (h hi)⟩

end NbhdBasis

end DomainTheory.BridgeTheorems
