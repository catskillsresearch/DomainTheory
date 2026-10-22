/-ai
The typical Σ₁¹ set is a Σ₁¹ set.

A set is Σ₁¹ when it is the set of x at which two Scott-continuous maps agree for some argument. The maps sending u to u applied to {0} and to u applied to {1} are Scott continuous in the function argument, and they reproduce the defining condition of the typical set.
ai-/

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
