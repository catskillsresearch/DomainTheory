
module

public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottOpen
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.theorem_6_1
public import DomainTheory.DataTypesAsLattices.Classification.typicalG

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


theorem typicalG_isScottOpen : IsScottOpen typicalG := by
  simpa [typicalG] using (theorem_6_1).1 (fun x => x) id_isScottContinuous

end DomainTheory.DataTypesAsLattices
