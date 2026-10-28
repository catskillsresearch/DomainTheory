module

public import DomainTheory.ContinuousLattice.Injective.RetractSubspace
public import DomainTheory.ContinuousLattice.Injective.InjectiveSpace
public import Mathlib.Topology.Separation.Basic
import DomainTheory.ContinuousLattice.Injective.isInjectiveSpace_sierpinski_power
import DomainTheory.ContinuousLattice.Injective.proposition_1_5

@[expose] public section

open Topology TopologicalSpace

universe u

theorem corollary_1_6 (D : Type u) [TopologicalSpace D] [T0Space D] :
    InjectiveSpace.{u,u} D ↔ ∃ (ι : Type u), Nonempty (RetractSubspace D (ι → Prop)) := by
  constructor
  · intro hD
    obtain ⟨r, hr⟩ := hD.extension (productOfMemOpens D) (proposition_1_5 D).2 (ContinuousMap.id D)
    refine ⟨Opens D, ⟨⟨productOfMemOpens D, (proposition_1_5 D).2, r, hr⟩⟩⟩
  · rintro ⟨ι, ⟨R⟩⟩
    exact InjectiveSpace.of_retract (isInjectiveSpace_sierpinski_power ι) R.section' R.retraction
      R.retraction_section
