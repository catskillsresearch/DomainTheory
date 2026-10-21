/-ai
The typical 𝔉 set lies in 𝔉.

By the 𝔉 theorem, a set lies in 𝔉 when it is the set of x at which some Scott-continuous map takes the value ⊥. The identity is Scott continuous, and it takes the value ⊥ exactly at ⊥.
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








































































































theorem typicalF_mem_ScottF : typicalF ∈ ScottF :=
  (theorem_6_2 typicalF).mpr ⟨fun x => x, id_isScottContinuous, rfl⟩

end DomainTheory.DataTypesAsLattices
