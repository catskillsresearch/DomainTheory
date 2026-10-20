module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace








































































































/-- **Scott 1976, Table 3.** `{⊤}` is a `Gδ`. -/
theorem typicalGdelta_eq : typicalGdelta = ⋂ n, {x : Pomega | n ∈ x} := by
  ext x
  constructor
  · intro hx
    refine Set.mem_iInter.mpr fun n => ?_
    have hx' : x = topElem := hx
    simp [hx']
  · intro hx
    ext k
    constructor
    · intro _; trivial
    · intro _
      exact Set.mem_iInter.mp hx k

end DomainTheory.DataTypesAsLattices
