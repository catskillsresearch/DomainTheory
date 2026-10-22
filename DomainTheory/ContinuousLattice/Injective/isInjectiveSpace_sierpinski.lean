module

public import DomainTheory.ContinuousLattice.Injective.InjectiveSpace
public import Mathlib.Topology.Order
import Mathlib.Topology.Maps.Basic

@[expose] public section


open Topology TopologicalSpace


/-- Scott's two-point Sierpiński space 𝕆: `Prop` with the Sierpiński topology. -/
abbrev Sierpinski := Prop

/-- **Scott 1972, Proposition 1.2.** The Sierpiński space is injective. -/
theorem isInjectiveSpace_sierpinski : InjectiveSpace.{u} Sierpinski := by
  constructor
  intro X Y _ _ e he f
  have hfopen : IsOpen {x | f x} := continuous_Prop.1 f.continuous
  rw [he.isInducing.isOpen_iff] at hfopen
  obtain ⟨V, hVopen, hVeq⟩ := hfopen
  refine ⟨⟨fun y => y ∈ V, continuous_Prop.2 hVopen⟩, fun x => ?_⟩
  have : (e x ∈ V) = (x ∈ {x | f x}) := by rw [← hVeq]; rfl
  simpa using this
