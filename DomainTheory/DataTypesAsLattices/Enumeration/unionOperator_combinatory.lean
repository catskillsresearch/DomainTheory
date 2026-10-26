
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_4
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_4_more
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.unionTerm
public import DomainTheory.DataTypesAsLattices.Enumeration.unionTerm_interp

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem unionOperator_combinatory :
    IsCombinatory (graph (fun x => graph (fun y => x ∪ y))) := by
  rw [← unionTerm_interp]
  exact theorem_2_4.closed unionTerm

end DomainTheory.DataTypesAsLattices
