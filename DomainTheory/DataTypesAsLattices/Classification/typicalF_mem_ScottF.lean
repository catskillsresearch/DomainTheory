
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic
public import DomainTheory.DataTypesAsLattices.Classification.theorem_6_2

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


theorem typicalF_mem_ScottF : typicalF ∈ ScottF :=
  (theorem_6_2 typicalF).mpr ⟨fun x => x, id_isScottContinuous, rfl⟩

end DomainTheory.DataTypesAsLattices
