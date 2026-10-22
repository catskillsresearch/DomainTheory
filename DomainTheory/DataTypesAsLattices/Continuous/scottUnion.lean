module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega
public import DomainTheory.DataTypesAsLattices.Continuous.scottPiece

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def scottUnion (f : Pomega → Pomega) (x : Pomega) : Pomega :=
  ⋃ n, scottPiece f x n

end DomainTheory.DataTypesAsLattices
