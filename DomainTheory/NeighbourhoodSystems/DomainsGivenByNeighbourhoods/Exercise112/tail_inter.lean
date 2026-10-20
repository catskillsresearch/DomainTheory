module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.tail
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.mem_tail

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- `tail n ∩ tail m = tail (max n m)` (the intersection of two tails is the shorter one). -/
theorem tail_inter (n m : ℕ) : tail n ∩ tail m = tail (max n m) := by
  ext k
  simp only [Set.mem_inter_iff, mem_tail]
  omega

end DomainTheory.NeighbourhoodSystems.Exercise112
