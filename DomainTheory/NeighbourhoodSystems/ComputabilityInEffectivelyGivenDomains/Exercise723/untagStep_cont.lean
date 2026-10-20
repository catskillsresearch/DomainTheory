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






























































theorem untagStep_cont {w : ℕ} (hdone : w.unpair.2.unpair.1 = 0) {k : ℕ}
    (ha : unnum1 w.unpair.1 = k + 1) :
    untagStep w = Nat.pair (unnum2 w.unpair.1)
      (Nat.pair 0
        (Nat.pair (Nat.pair k w.unpair.2.unpair.2.unpair.1 + 1) w.unpair.2.unpair.2.unpair.2)) := by
  unfold untagStep
  rw [hdone, selectFn_zero, ha]
  have hz : isZero (k + 1) = 0 := by unfold isZero; omega
  have hsub : k + 1 - 1 = k := by omega
  rw [hz, selectFn_zero, hsub]

end DomainTheory.NeighbourhoodSystems.Exercise723
