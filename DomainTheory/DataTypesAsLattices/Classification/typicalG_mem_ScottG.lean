/-ai
The typical 𝔊 set belongs to the class 𝔊 of Scott-open sets.

Membership is the theorem that the typical set is Scott open.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic
public import DomainTheory.DataTypesAsLattices.Classification.typicalG_isScottOpen

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace








































































































theorem typicalG_mem_ScottG : typicalG ∈ ScottG :=
  typicalG_isScottOpen

end DomainTheory.DataTypesAsLattices
