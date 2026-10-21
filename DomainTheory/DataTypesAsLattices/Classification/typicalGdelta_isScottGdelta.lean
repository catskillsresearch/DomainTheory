/-ai
The typical 𝔊δ set is a Scott Gδ set.

By the 𝔊δ theorem, a Scott Gδ set is the set of x at which some Scott-continuous map takes the value ⊤. The identity is Scott continuous and takes that value exactly at ⊤.
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








































































































theorem typicalGdelta_isScottGdelta : IsScottGdelta typicalGdelta :=
  (theorem_6_3 typicalGdelta).mpr ⟨fun x => x, id_isScottContinuous, rfl⟩

end DomainTheory.DataTypesAsLattices
