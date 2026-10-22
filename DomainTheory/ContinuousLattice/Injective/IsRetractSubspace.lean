module


public import Mathlib.Topology.ContinuousMap.T0Sierpinski
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Sets.Opens

@[expose] public section

universe u

open Topology TopologicalSpace

/-- Scott's notion of retract: a subspace with a continuous retraction. -/
structure IsRetractSubspace (D' D : Type u) [TopologicalSpace D'] [TopologicalSpace D] where
  section' : C(D', D)
  isEmbedding_section : IsEmbedding section'
  retraction : C(D, D')
  retraction_section : ∀ d, retraction (section' d) = d
