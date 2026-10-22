/-ai
A space D is injective when every continuous map into D extends along every topological embedding: for an embedding of X into Y and a continuous map from X to D, some continuous map from Y to D agrees with it on the image of the embedding.
ai-/
module

public import Mathlib.Topology.ContinuousMap.T0Sierpinski
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Sets.Opens

@[expose] public section

open Topology TopologicalSpace

universe u v

/-- **Scott 1972, Definition 1.1.** A topological space `D` is *injective* when, for every
topological embedding `e : X → Y` and every continuous `f : X → D`, there is a continuous
`g : Y → D` extending `f` along `e`. -/
def IsInjectiveSpace (D : Type v) [TopologicalSpace D] : Prop :=
  ∀ {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (e : X → Y),
    IsEmbedding e → ∀ f : C(X, D), ∃ g : C(Y, D), ∀ x, g (e x) = f x
