module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem valNat_combinatory : ∀ n, IsCombinatory (valNat n)
  | 0 => valNat_zero ▸ Gcomb_combinatory
  | n + 1 =>
    valNat_succ n ▸
      .app (valNat_combinatory (unpair n).1) (valNat_combinatory (unpair n).2)
decreasing_by
  · exact (pair_lt_left (unpair n).1 (unpair n).2).trans_le (by
      have := pair_unpair n
      omega)
  · exact (pair_lt_right (unpair n).1 (unpair n).2).trans_le (by
      have := pair_unpair n
      omega)

end DomainTheory.DataTypesAsLattices
