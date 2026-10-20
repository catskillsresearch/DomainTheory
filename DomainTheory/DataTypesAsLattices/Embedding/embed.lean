module

public import Mathlib.Topology.Bases
import all Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
import all Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
import all Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
import all Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace Topology Function

/-- **Scott 1976, Theorem 1.6.** The embedding `ε(x) = {n | x ∈ U n}`. -/
def embed {X : Type*} (U : ℕ → Set X) (x : X) : Pomega :=
  {n | x ∈ U n}

end DomainTheory.DataTypesAsLattices
