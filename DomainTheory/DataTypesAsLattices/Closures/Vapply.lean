
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def Vapply (a x : Pomega) : Pomega :=
  ⋂₀ {y | x ⊆ y ∧ funOf a y ⊆ y}

end DomainTheory.DataTypesAsLattices
