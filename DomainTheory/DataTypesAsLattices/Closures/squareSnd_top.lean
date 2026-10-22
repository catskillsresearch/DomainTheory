module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem squareSnd_top : squareSnd topElem = topElem := by
  ext m
  constructor
  · intro; exact Set.mem_univ m
  · intro; exact Set.mem_univ (2 * m + 1)

end DomainTheory.DataTypesAsLattices
