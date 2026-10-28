module

public import Mathlib.Topology.ContinuousMap.T0Sierpinski
public import DomainTheory.ContinuousLattice.Injective.InjectiveSpace
import DomainTheory.ContinuousLattice.Injective.isInjectiveSpace_sierpinski_power

@[expose] public section

open Topology TopologicalSpace

universe u

theorem proposition_1_5 (X : Type u) [TopologicalSpace X] [T0Space X] :
    InjectiveSpace.{u,u} (Opens X → Prop) ∧
      IsEmbedding (productOfMemOpens X) := by
  refine ⟨?_, productOfMemOpens_isEmbedding X⟩
  exact isInjectiveSpace_sierpinski_power (Opens X)
