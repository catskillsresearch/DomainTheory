module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.openR
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.openR_map_isScottContinuous

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem openR_app (u : Pomega) :
    funOf openR u = {m | ∃ n, e n ⊆ e m ∧ n ∈ u} :=
  beta openR_map_isScottContinuous u

end DomainTheory.DataTypesAsLattices
