/-ai
The Sierpiński space of propositions is injective.

A continuous map into this space has open truth set. Along an embedding, that open set is the preimage of an open set V. Membership in V is a continuous map into the Sierpiński space, and it extends the original map because membership of an image point in V is the truth of the original value.
ai-/
module

public import Mathlib.Topology.ContinuousMap.T0Sierpinski
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Sets.Opens
public import DomainTheory.ContinuousLattice.Injective.IsInjectiveSpace

@[expose] public section


open Topology TopologicalSpace


/-- Scott's two-point Sierpiński space 𝕆: `Prop` with the Sierpiński topology. -/
abbrev Sierpinski := Prop

/-- **Scott 1972, Proposition 1.2.** The Sierpiński space is injective. -/
theorem isInjectiveSpace_sierpinski : IsInjectiveSpace.{u} Sierpinski := by
  intro X Y _ _ e he f
  have hfopen : IsOpen {x | f x} := continuous_Prop.1 f.continuous
  rw [he.isInducing.isOpen_iff] at hfopen
  obtain ⟨V, hVopen, hVeq⟩ := hfopen
  refine ⟨⟨fun y => y ∈ V, continuous_Prop.2 hVopen⟩, fun x => ?_⟩
  have : (e x ∈ V) = (x ∈ {x | f x}) := by rw [← hVeq]; rfl
  simpa using this
