module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































theorem squareSnd_bot : squareSnd botElem = botElem := by
  ext m
  simp [squareSnd, botElem]

end DomainTheory.DataTypesAsLattices
