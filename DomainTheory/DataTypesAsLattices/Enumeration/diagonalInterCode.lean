module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.num
public import DomainTheory.DataTypesAsLattices.Enumeration.interCode

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

noncomputable def diagonalInterCode (n : ℕ) : ℕ :=
  applyNat (applyNat interCode (num n)) n

end DomainTheory.DataTypesAsLattices
