module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.Specialization.scottTopologicalSpace
public import DomainTheory.ContinuousLattice.Injective.InjectiveSpace
public import DomainTheory.ContinuousLattice.Constructions.scottExtend_continuous
public import DomainTheory.ContinuousLattice.Constructions.scottExtend_eq_of_continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]

theorem proposition_2_11 {E : Type*} [CompleteLattice E] (hE : ContinuousLattice E) :
    @InjectiveSpace E scottTopologicalSpace := by
  let : TopologicalSpace E := scottTopologicalSpace
  constructor
  intro X Y _ _ e he f
  exact ⟨⟨scottExtend e f, scottExtend_continuous hE e f⟩,
    fun x => scottExtend_eq_of_continuous hE e he f f.continuous x⟩

end DomainTheory.ContinuousLattice
