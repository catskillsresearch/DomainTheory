/-ai
The typical 𝔉 ∩ 𝔊 set is an intersection of a Scott-closed set and a Scott-open set.

By Theorem 6.4, such a set is the set of x at which some Scott-continuous map takes the value {0}. The identity is Scott continuous and takes that value exactly at {0}.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic
public import DomainTheory.DataTypesAsLattices.Classification.theorem_6_4

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


theorem typicalFcapG_isFcapG : IsFcapG typicalFcapG :=
  (theorem_6_4 typicalFcapG).mpr ⟨fun x => x, id_isScottContinuous, rfl⟩

end DomainTheory.DataTypesAsLattices
