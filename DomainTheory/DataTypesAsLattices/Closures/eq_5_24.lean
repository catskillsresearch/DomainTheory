module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.theorem_5_5_universe
public import DomainTheory.DataTypesAsLattices.Closures.theorem_5_3_closure

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































/-- **Scott 1976, (5.24).** Function space of closures is a closure. -/
theorem eq_5_24 {a b : Pomega} (ha : typed a Vcomb) (hb : typed b Vcomb) :
    typed (arrowR a b) Vcomb :=
  (theorem_5_5_universe.2 (arrowR a b)).mp
    (theorem_5_3_closure ((theorem_5_5_universe.2 a).mpr ha)
      ((theorem_5_5_universe.2 b).mpr hb))

end DomainTheory.DataTypesAsLattices
