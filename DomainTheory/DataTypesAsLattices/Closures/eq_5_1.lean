module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2
public import DomainTheory.DataTypesAsLattices.Pomega.e
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_5_1 (u : Pomega) : u ⊆ graph (fun x => funOf u x) :=
  theorem_1_2.ii u

end DomainTheory.DataTypesAsLattices
