module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.unionBits
public import DomainTheory.DataTypesAsLattices.Enumeration.bitList
public import DomainTheory.DataTypesAsLattices.Enumeration.e_eq_unionBits

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem e_combinatory (j : ℕ) : IsCombinatory (e j) := by
  simpa [e_eq_unionBits] using unionBits.combinatory (bitList j)

end DomainTheory.DataTypesAsLattices
