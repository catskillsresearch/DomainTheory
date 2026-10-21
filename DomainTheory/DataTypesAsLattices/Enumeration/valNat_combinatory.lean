/-ai
Every value of the numerical evaluator is combinatory.

At zero, the zero clause and combinatoriness of the G combinator give the result. At a successor, the successor clause writes the value as an application of the values at the two unpairing components, and both are combinatory by the inductive hypothesis. Each recursive call is at an unpairing component, which is strictly smaller than the paired code and hence smaller than the successor.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
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
