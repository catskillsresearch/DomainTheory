module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace








































































































theorem typicalBdelta_isBdelta : IsBdelta typicalBdelta :=
  (theorem_6_7 typicalBdelta).mpr
    ⟨fun u => funOf u (ofNat 0), fun u => funOf u (ofNat 1),
      funOf_isScottContinuous_left (ofNat 0),
      funOf_isScottContinuous_left (ofNat 1), rfl⟩

end DomainTheory.DataTypesAsLattices
