/-ai
The intersection of two tails is the tail of the larger index.

Compare the two sets by extensionality. After unfolding membership, a number lies in both tails exactly when it is at least both indices, which is the comparison with their maximum.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.tail
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.mem_tail

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- `tail n ∩ tail m = tail (max n m)` (the intersection of two tails is the shorter one). -/
theorem tail_inter (n m : ℕ) : tail n ∩ tail m = tail (max n m) := by
  ext k
  simp only [Set.mem_inter_iff, mem_tail]
  omega

end DomainTheory.NeighbourhoodSystems.Exercise112
