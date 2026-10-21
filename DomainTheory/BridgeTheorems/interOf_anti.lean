/-ai
If a finite set of neighbourhood indices is contained in another, then the folded intersection of the larger set is contained in the folded intersection of the smaller set.

A point of the larger intersection lies in the master set and in every neighbourhood indexed by the larger set, hence in every neighbourhood indexed by the smaller set.
ai-/
module

public import Mathlib.Data.Finset.Fold
import all Mathlib.Data.Finset.Fold
public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.NbhdBasis
public import DomainTheory.BridgeTheorems.interOf
public import DomainTheory.BridgeTheorems.interOf_empty
public import DomainTheory.BridgeTheorems.mem_interOf

@[expose] public section

set_option linter.unusedSectionVars false

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
