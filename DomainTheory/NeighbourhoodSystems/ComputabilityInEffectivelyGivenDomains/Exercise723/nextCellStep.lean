/-ai
The map nextCellStep is the pairing code of the cell step on pairs of natural numbers. On a packed pair it sends (0, m) to the packing of (m + 1, 0), and it sends (n + 1, m) to the packing of (n, m + 1). The zero test on the first component selects the two branches.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.halfIter_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.mem_elemSet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic.notation16

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive

open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)

open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

/-- Pair-coded version of `nextCell : ℕ × ℕ → ℕ × ℕ` (`(0, m) ↦ (m+1, 0)`, `(n+1, m) ↦ (n, m+1)`). -/
def nextCellStep (w : ℕ) : ℕ :=
  selectFn (isZero w.unpair.1) (Nat.pair (w.unpair.2 + 1) 0)
    (Nat.pair (w.unpair.1 - 1) (w.unpair.2 + 1))

end DomainTheory.NeighbourhoodSystems.Exercise723
