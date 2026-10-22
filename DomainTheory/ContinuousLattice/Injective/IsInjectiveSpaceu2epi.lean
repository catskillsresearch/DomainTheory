/-ai
A product of injective spaces is injective.

Given an embedding and a continuous map into the product, extend each coordinate map along the embedding by injectivity of the corresponding factor, and reassemble the extensions as a map into the product. The extension agrees with the original map because the coordinates agree.
ai-/
module

public import Mathlib.Topology.ContinuousMap.T0Sierpinski
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Sets.Opens
public import DomainTheory.ContinuousLattice.Injective.Basic

@[expose] public section


open Topology TopologicalSpace

universe v w


/-- **Scott 1972, Proposition 1.3.** Products of injective spaces are injective. -/
theorem InjectiveSpace.pi {ι : Type w} (D : ι → Type v) [∀ i, TopologicalSpace (D i)]
    (h : ∀ i, InjectiveSpace.{u} (D i)) :     InjectiveSpace.{u} (∀ i, D i) := by
  constructor
  intro X Y _ _ e he f
  choose g hg using fun i =>
    (h i).extension e he ⟨fun x => f x i, (continuous_apply i).comp f.continuous⟩
  refine ⟨⟨fun y i => g i y, continuous_pi fun i => (g i).continuous⟩, fun x => ?_⟩
  funext i
  exact hg i x
