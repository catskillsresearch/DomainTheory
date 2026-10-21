/-ai
The typical 𝔉 ∩ 𝔊δ set is an intersection of a Scott-closed set and a Scott Gδ set.

By Theorem 6.5, such a set is the set of x at which some Scott-continuous map takes the value ⊤ + 1. The identity is Scott continuous and takes that value exactly at ⊤ + 1.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic
public import DomainTheory.DataTypesAsLattices.Classification.theorem_6_5

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace








































































































theorem typicalFcapGdelta_isFcapGdelta : IsFcapGdelta typicalFcapGdelta :=
  (theorem_6_5 typicalFcapGdelta).mpr ⟨fun x => x, id_isScottContinuous, rfl⟩

end DomainTheory.DataTypesAsLattices
