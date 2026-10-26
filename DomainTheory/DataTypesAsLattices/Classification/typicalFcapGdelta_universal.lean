
module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.theorem_6_5
public import DomainTheory.DataTypesAsLattices.Classification.IsFcapGdelta
public import DomainTheory.DataTypesAsLattices.Classification.typicalFcapGdelta

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


/-- **Scott 1976, Table 3 / Theorem 6.5.** `𝔉 ∩̇ 𝔊_δ` is the class of
continuous preimages of `{⊤ + 1}`. -/
theorem typicalFcapGdelta_universal (U : Set Pomega) :
    IsFcapGdelta U ↔
      ∃ f, IsScottContinuous f ∧ U = {x | f x ∈ typicalFcapGdelta} :=
  theorem_6_5 U

end DomainTheory.DataTypesAsLattices
