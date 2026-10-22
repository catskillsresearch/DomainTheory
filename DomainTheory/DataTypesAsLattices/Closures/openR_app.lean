module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.openR_map_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem openR_app (u : Pomega) :
    funOf openR u = {m | ∃ n, e n ⊆ e m ∧ n ∈ u} :=
  beta openR_map_isScottContinuous u

end DomainTheory.DataTypesAsLattices
