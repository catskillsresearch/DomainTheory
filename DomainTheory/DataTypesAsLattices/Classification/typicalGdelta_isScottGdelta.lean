
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic
public import DomainTheory.DataTypesAsLattices.Classification.theorem_6_3

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


theorem typicalGdelta_isScottGdelta : IsScottGdelta typicalGdelta :=
  (theorem_6_3 typicalGdelta).mpr ⟨fun x => x, id_isScottContinuous, rfl⟩

end DomainTheory.DataTypesAsLattices
