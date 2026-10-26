
module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Pi11
public import DomainTheory.DataTypesAsLattices.Classification.typicalPi11

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


/-- **Scott 1976, Table 3.** `Π₁¹` is the class of continuous preimages of
`{u | ∀ y ∃ z. u(y)(z) = 0}`. -/
theorem typicalPi11_universal (U : Set Pomega) :
    Pi11 U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x ∈ typicalPi11} := by
  constructor
  · rintro ⟨⟨h, hh, rfl⟩⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨⟨f, hf, rfl⟩⟩

end DomainTheory.DataTypesAsLattices
