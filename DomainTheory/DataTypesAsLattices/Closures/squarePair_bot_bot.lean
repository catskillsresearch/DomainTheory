module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem squarePair_bot_bot : squarePair botElem botElem = (botElem : Pomega) := by
  ext k
  simp [squarePair, botElem]

end DomainTheory.DataTypesAsLattices
