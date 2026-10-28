module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.FixedPoint.iterateBot
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.valStep
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem valStage_subset : ∀ s n,
    funOf (iterateBot valStep s) (ofNat n) ⊆ valNat n
  | 0, n => by simp [iterateBot, funOf, botElem]
  | s + 1, 0 => by
      rw [iterateBot, valStep.app_zero, valNat.zero]
  | s + 1, p + 1 => by
      rw [iterateBot, valStep.app_succ, valNat.succ]
      exact subset_trans
        (funOf.monotone_left
          (valStage_subset s (unpair p).1)
          (funOf (iterateBot valStep s) (ofNat (unpair p).2)))
        (funOf.monotone_right (valNat (unpair p).1)
          (valStage_subset s (unpair p).2))

end DomainTheory.DataTypesAsLattices
