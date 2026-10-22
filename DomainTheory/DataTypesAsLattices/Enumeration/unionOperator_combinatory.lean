/-ai
The graph of x ↦ (the graph of y ↦ x ∪ y) is combinatory.

It equals the interpretation of the closed union term in the constantly bottom environment, and the interpretation of a closed term is combinatory by Theorem 2.4.
ai-/

module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
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
  exact theorem_2_4_closed unionTerm

end DomainTheory.DataTypesAsLattices
