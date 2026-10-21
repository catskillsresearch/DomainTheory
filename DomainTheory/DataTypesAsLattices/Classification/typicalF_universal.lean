/-ai
Scott's Table 3 and Theorem 6.2 state that 𝔉 is the class of continuous preimages of {⊥}: a set U lies in 𝔉 if and only if U is the set of x whose image under some Scott-continuous f lies in the typical 𝔉 set.

The statement is the 𝔉 theorem, because membership in the singleton {⊥} is equality with ⊥.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic
public import DomainTheory.DataTypesAsLattices.Classification.theorem_6_2

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


/-- **Scott 1976, Table 3 / Theorem 6.2.** `𝔉` is the class of continuous
preimages of `{⊥}`. -/
theorem typicalF_universal (U : Set Pomega) :
    U ∈ ScottF ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x ∈ typicalF} :=
  theorem_6_2 U

end DomainTheory.DataTypesAsLattices
