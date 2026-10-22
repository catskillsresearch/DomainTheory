/-ai
For every T₀-space, the power of the Sierpiński space indexed by its open sets is injective, and the map sending each point to the family of its memberships in those open sets is a topological embedding.

The power is injective because every power of the Sierpiński space is injective, and the membership map is an embedding.
ai-/
module

public import Mathlib.Topology.ContinuousMap.T0Sierpinski
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Sets.Opens
public import DomainTheory.ContinuousLattice.Injective.Basic
public import DomainTheory.ContinuousLattice.Injective.isInjectiveSpace_sierpinski_power

@[expose] public section


open Topology TopologicalSpace

universe u


/-- **Scott 1972, Proposition 1.5.** Every `T₀`-space embeds into a power of 𝕆, and that
power is injective. -/
theorem proposition_1_5 (X : Type u) [TopologicalSpace X] [T0Space X] :
    InjectiveSpace.{u,u} (Opens X → Prop) ∧
      IsEmbedding (productOfMemOpens X) := by
  refine ⟨?_, productOfMemOpens_isEmbedding X⟩
  exact isInjectiveSpace_sierpinski_power (Opens X)
