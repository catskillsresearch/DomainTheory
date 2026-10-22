/-ai
Scott's Table 3 and Theorem 6.4 state that 𝔉 ∩ 𝔊 is the class of continuous preimages of {{0}}: a set is of that class if and only if it is the set of x whose image under some Scott-continuous f lies in the typical set.

The statement is Theorem 6.4, because membership in the singleton {{0}} is equality with {0}.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
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
