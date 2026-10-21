/-ai
Scott's Table 3 and Theorem 6.3 state that 𝔊δ is the class of continuous preimages of {⊤}: a set is a Scott Gδ set if and only if it is the set of x whose image under some Scott-continuous f lies in the typical set.

The statement is the 𝔊δ theorem, because membership in the singleton {⊤} is equality with ⊤.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic
public import DomainTheory.DataTypesAsLattices.Classification.theorem_6_3

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace








































































































/-- **Scott 1976, Table 3 / Theorem 6.3.** `𝔊_δ` is the class of continuous
preimages of `{⊤}`. -/
theorem typicalGdelta_universal (U : Set Pomega) :
    IsScottGdelta U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x ∈ typicalGdelta} :=
  theorem_6_3 U

end DomainTheory.DataTypesAsLattices
