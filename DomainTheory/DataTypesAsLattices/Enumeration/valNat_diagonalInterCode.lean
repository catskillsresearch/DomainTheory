/-ai
The numerical evaluator sends the diagonal intersection code of n to the intersection of the numeral of n with its value at n.

Unfold the diagonal intersection code, apply the application law for the evaluator twice, replace the intersection code by the intersection combinator, and rewrite by equations (3.12) and (2.17).
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_12
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_interCode

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices
























































theorem valNat_diagonalInterCode (n : ℕ) :
    valNat (diagonalInterCode n) = ofNat n ∩ valNat n := by
  rw [diagonalInterCode, valNat_apply, valNat_apply, valNat_interCode,
    eq_3_12, eq_2_17]

end DomainTheory.DataTypesAsLattices
