/-ai
Scott's Table 3 and Theorem 6.5 state that 𝔉 ∩ 𝔊δ is the class of continuous preimages of {⊤ + 1}: a set is of that class if and only if it is the set of x whose image under some Scott-continuous f lies in the typical set.

The statement is Theorem 6.5, because membership in the singleton {⊤ + 1} is equality with ⊤ + 1.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic
public import DomainTheory.DataTypesAsLattices.Classification.theorem_6_5

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
