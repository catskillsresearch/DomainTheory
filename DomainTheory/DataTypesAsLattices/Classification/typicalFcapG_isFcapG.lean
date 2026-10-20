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
