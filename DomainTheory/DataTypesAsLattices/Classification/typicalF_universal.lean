
module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.theorem_6_2
public import DomainTheory.DataTypesAsLattices.Classification.typicalF
public import DomainTheory.DataTypesAsLattices.Classification.ScottF

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


/-- **Scott 1976, Table 3 / Theorem 6.2.** `𝔉` is the class of continuous
preimages of `{⊥}`. -/
theorem typicalF_universal (U : Set Pomega) :
    U ∈ ScottF ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x ∈ typicalF} :=
  theorem_6_2 U

end DomainTheory.DataTypesAsLattices
