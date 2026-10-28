module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb
public import DomainTheory.DataTypesAsLattices.Closures.theorem_5_5
public import DomainTheory.DataTypesAsLattices.Closures.theorem_5_3
public import DomainTheory.DataTypesAsLattices.Closures.theorem_5_5_universe
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_5_24 {a b : Pomega} (ha : typed a Vcomb) (hb : typed b Vcomb) :
    typed (arrowR a b) Vcomb :=
  (theorem_5_5.universe.2 (arrowR a b)).mp
    (theorem_5_3.closure ((theorem_5_5.universe.2 a).mpr ha)
      ((theorem_5_5.universe.2 b).mpr hb))

end DomainTheory.DataTypesAsLattices
