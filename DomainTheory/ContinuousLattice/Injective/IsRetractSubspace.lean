/-ai
A retract subspace consists of a continuous section of D' into D that is a topological embedding, together with a continuous retraction of D onto D' that is a left inverse of the section.
ai-/
module


public import Mathlib.Topology.ContinuousMap.T0Sierpinski
import all Mathlib.Topology.ContinuousMap.T0Sierpinski
public import Mathlib.Topology.ContinuousMap.Basic
import all Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Sets.Opens
import all Mathlib.Topology.Sets.Opens

@[expose] public section

universe u v w

open Topology TopologicalSpace

/-- Scott's notion of retract: a subspace with a continuous retraction. -/
structure IsRetractSubspace (D' D : Type u) [TopologicalSpace D'] [TopologicalSpace D] where
  section' : C(D', D)
  isEmbedding_section : IsEmbedding section'
  retraction : C(D, D')
  retraction_section : ∀ d, retraction (section' d) = d
