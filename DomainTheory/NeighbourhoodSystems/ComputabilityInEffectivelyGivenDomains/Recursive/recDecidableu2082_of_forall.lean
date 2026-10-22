module

public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.Basic
public import Mathlib.Computability.Partrec
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.recDecidable_of_forall

@[expose] public section


namespace Domain.Recursive


/-- An always-true binary relation is recursively decidable (constant decider `1`). -/
theorem recDecidable₂_of_forall {r : ℕ → ℕ → Prop} (h : ∀ n m, r n m) : RecDecidable₂ r :=
  recDecidable_of_forall (fun t => h t.unpair.1 t.unpair.2)

end Domain.Recursive
