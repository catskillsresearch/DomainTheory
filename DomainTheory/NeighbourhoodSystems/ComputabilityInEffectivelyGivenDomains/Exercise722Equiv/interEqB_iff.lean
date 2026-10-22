module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.subsetB_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability
open Sum Set


theorem interEqB_iff (e1 e2 : SExpr) : interEqB e1 e2 = true ↔ denote e1 = denote e2 := by
  unfold interEqB
  rw [Bool.and_eq_true, subsetB_iff, subsetB_iff, ← Set.Subset.antisymm_iff]

end Exercise722
end DomainTheory.NeighbourhoodSystems
