module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.nbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.mem_nbhd

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example78

open Domain.Recursive NeighborhoodSystem

/-- **Scott's `Eₙ ∪ Eₘ = E_{n ||| m}`.** The intersection of two cofinite neighbourhoods is again
one: `nbhd n ∩ nbhd m = nbhd (n ||| m)` (bitwise OR of the excluded finite sets). -/
theorem nbhd_inter (n m : ℕ) : nbhd n ∩ nbhd m = nbhd (myLor n m) := by
  ext k
  simp only [nbhd, Set.mem_inter_iff, Set.mem_ofPred_eq, myLor_eq_lor, Nat.testBit_lor,
    Bool.or_eq_false_iff]

end DomainTheory.NeighbourhoodSystems.Example78
