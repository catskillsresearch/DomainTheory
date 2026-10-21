/-ai
Applying the open retract to u yields the set of codes m for which some finite set e n contained in e m has its index n in u.

This is the beta law for the Scott-continuous map that defines the open retract.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.openR_map_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem openR_app (u : Pomega) :
    funOf openR u = {m | ∃ n, e n ⊆ e m ∧ n ∈ u} :=
  beta openR_map_isScottContinuous u

end DomainTheory.DataTypesAsLattices
