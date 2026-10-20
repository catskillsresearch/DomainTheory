module

public import Mathlib.Topology.Bases
import all Mathlib.Topology.Bases
public import Mathlib.Topology.Order
import all Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega
public import DomainTheory.DataTypesAsLattices.Continuous.scottPiece

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def scottUnion (f : Pomega → Pomega) (x : Pomega) : Pomega :=
  ⋃ n, scottPiece f x n

end DomainTheory.DataTypesAsLattices
