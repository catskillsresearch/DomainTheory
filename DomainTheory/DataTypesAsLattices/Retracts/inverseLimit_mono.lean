module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint.iterateBot
public import DomainTheory.DataTypesAsLattices.FixedPoint.iterateBot_mono
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.RetractInverseLimit
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem inverseLimit_mono {F : Pomega → Pomega}
    (hf : IsScottContinuous F) (v : RetractInverseLimit F) :
    ∀ n, v.1 n ⊆ v.1 (n + 1) := by
  intro n
  rw [v.property.2 n]
  have hcode : iterateBot F n ⊆ iterateBot F (n + 1) :=
    iterateBot_mono hf n
  have h := funOf.monotone_left hcode (v.1 (n + 1))
  rw [← v.property.1 (n + 1)] at h
  exact h

end DomainTheory.DataTypesAsLattices
