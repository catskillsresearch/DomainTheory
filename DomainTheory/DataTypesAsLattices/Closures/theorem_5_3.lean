module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Retracts.theorem_4_3
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_more
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Theorem 5.3 (The function space theorem for algebraic
lattices).** The function-space retract of two closures is a retract. -/
theorem theorem_5_3 {a b : Pomega} (ha : Closure a) (hb : Closure b) :
    Retract (arrowR a b) := by
  constructor
  change arrowR a b = graph (fun x => funOf (arrowR a b) (funOf (arrowR a b) x))
  apply graph_ext
  intro u
  rw [theorem_4_3.i ha.out.2 hb.out.2, arrowR.app]

namespace theorem_5_3

theorem closure {a b : Pomega} (ha : Closure a) (hb : Closure b) :
    Closure (arrowR a b) :=
  ⟨⟨Icomb_subset_arrowR ha hb, theorem_5_3 ha hb⟩⟩

end theorem_5_3

end DomainTheory.DataTypesAsLattices
