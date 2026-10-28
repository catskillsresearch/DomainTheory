module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.boxTensor
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb
public import DomainTheory.DataTypesAsLattices.Closures.theorem_5_4
public import DomainTheory.DataTypesAsLattices.Closures.theorem_5_5
public import DomainTheory.DataTypesAsLattices.Closures.theorem_5_5_universe
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_5_22 {a b : Pomega} (ha : typed a Vcomb) (hb : typed b Vcomb) :
    typed (boxTensor a b) Vcomb :=
  (theorem_5_5.universe.2 (boxTensor a b)).mp
    (theorem_5_4 ((theorem_5_5.universe.2 a).mpr ha)
      ((theorem_5_5.universe.2 b).mpr hb))

end DomainTheory.DataTypesAsLattices
