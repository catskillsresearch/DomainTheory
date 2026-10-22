/-ai
A T₀-space is injective if and only if it is a retract of some power of the Sierpiński space.

If the space is injective, the identity extends along its embedding into the product of one copy of the Sierpiński space for each open set, and the embedding together with that extension is a retract. Conversely, every power of the Sierpiński space is injective, and a retract of an injective space is injective.
ai-/
module

public import Mathlib.Topology.ContinuousMap.T0Sierpinski
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Sets.Opens
public import DomainTheory.ContinuousLattice.Injective.Basic
public import DomainTheory.ContinuousLattice.Injective.IsInjectiveSpaceu2eof_retract
public import DomainTheory.ContinuousLattice.Injective.isInjectiveSpace_sierpinski_power
public import DomainTheory.ContinuousLattice.Injective.proposition_1_5

@[expose] public section


open Topology TopologicalSpace

universe u


/-- **Scott 1972, Corollary 1.6.** Injective spaces are exactly retracts of powers of 𝕆. -/
theorem corollary_1_6 (D : Type u) [TopologicalSpace D] [T0Space D] :
    IsInjectiveSpace.{u,u} D ↔ ∃ (ι : Type u), Nonempty (IsRetractSubspace D (ι → Prop)) := by
  constructor
  · intro hD
    obtain ⟨r, hr⟩ := hD (productOfMemOpens D) (proposition_1_5 D).2 (ContinuousMap.id D)
    refine ⟨Opens D, ⟨⟨productOfMemOpens D, (proposition_1_5 D).2, r, hr⟩⟩⟩
  · rintro ⟨ι, ⟨R⟩⟩
    exact IsInjectiveSpace.of_retract (isInjectiveSpace_sierpinski_power ι) R.section' R.retraction
      R.retraction_section
