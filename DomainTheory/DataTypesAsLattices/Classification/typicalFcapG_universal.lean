
module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic
public import DomainTheory.DataTypesAsLattices.Classification.theorem_6_4

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


/-- **Scott 1976, Table 3 / Theorem 6.4.** `𝔉 ∩̇ 𝔊` is the class of continuous
preimages of `{0}`. -/
theorem typicalFcapG_universal (U : Set Pomega) :
    IsFcapG U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x ∈ typicalFcapG} :=
  theorem_6_4 U

end DomainTheory.DataTypesAsLattices
