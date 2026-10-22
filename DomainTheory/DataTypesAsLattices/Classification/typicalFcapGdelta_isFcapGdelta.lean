
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic
public import DomainTheory.DataTypesAsLattices.Classification.theorem_6_5

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


theorem typicalFcapGdelta_isFcapGdelta : IsFcapGdelta typicalFcapGdelta :=
  (theorem_6_5 typicalFcapGdelta).mpr ⟨fun x => x, id_isScottContinuous, rfl⟩

end DomainTheory.DataTypesAsLattices
