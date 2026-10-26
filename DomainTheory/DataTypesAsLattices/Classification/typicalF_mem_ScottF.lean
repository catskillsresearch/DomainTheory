
module

public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.theorem_6_2
public import DomainTheory.DataTypesAsLattices.Classification.typicalF
public import DomainTheory.DataTypesAsLattices.Classification.ScottF

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


theorem typicalF_mem_ScottF : typicalF ∈ ScottF := by
  refine (theorem_6_2 typicalF).mpr ⟨fun x => x, id_isScottContinuous, ?_⟩
  ext x; simp [typicalF]

end DomainTheory.DataTypesAsLattices
