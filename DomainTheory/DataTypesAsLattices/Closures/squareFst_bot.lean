module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem squareFst_bot : squareFst botElem = botElem := by
  ext n
  simp [squareFst, botElem]

end DomainTheory.DataTypesAsLattices
