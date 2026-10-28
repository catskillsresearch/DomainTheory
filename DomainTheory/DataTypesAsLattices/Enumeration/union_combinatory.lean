
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.union_via_cond
public import DomainTheory.DataTypesAsLattices.Pomega.e
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem union_combinatory {x y : Pomega}
    (hx : IsCombinatory x) (hy : IsCombinatory y) :
    IsCombinatory (x ∪ y) := by
  simpa [union_via_cond] using
    IsCombinatory.app (IsCombinatory.app (IsCombinatory.app .cond hx) hy)
      (IsCombinatory.app .K .zero)

end DomainTheory.DataTypesAsLattices
