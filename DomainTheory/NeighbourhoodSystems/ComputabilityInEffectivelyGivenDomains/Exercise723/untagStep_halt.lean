/-ai
If the done flag is zero and the first component of the numeral decoding is zero, the transition pairs the second component with the flag one, the reversed accumulator, and that second component.

Unfold the transition. The outer selection on the zero flag and the zero hypothesis leave the inner selection. The zero test of zero is one, so the inner selection is the halt branch.
ai-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)


theorem untagStep_halt {w : ℕ} (hdone : w.unpair.2.unpair.1 = 0) (ha : unnum1 w.unpair.1 = 0) :
    untagStep w = Nat.pair (unnum2 w.unpair.1)
      (Nat.pair 1 (Nat.pair w.unpair.2.unpair.2.unpair.1 (unnum2 w.unpair.1))) := by
  unfold untagStep
  rw [hdone, selectFn_zero, ha]
  have : isZero 0 = 1 := by unfold isZero; omega
  rw [this, selectFn_one]

end DomainTheory.NeighbourhoodSystems.Exercise723
