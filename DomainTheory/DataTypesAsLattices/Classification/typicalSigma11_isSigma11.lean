
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


theorem typicalSigma11_isSigma11 : IsSigma11 typicalSigma11 :=
  ⟨fun u => funOf u (ofNat 0), fun u => funOf u (ofNat 1),
    funOf_isScottContinuous_left (ofNat 0),
    funOf_isScottContinuous_left (ofNat 1), rfl⟩

end DomainTheory.DataTypesAsLattices
