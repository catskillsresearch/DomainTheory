module

public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Order.CompleteLattice.Basic

@[expose] public section

open Topology TopologicalSpace

universe u v

class InjectiveSpace (D : Type v) [TopologicalSpace D] : Prop where
  /-- Every continuous map into `D` extends along every topological embedding. -/
  extension :
    ∀ {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (e : X → Y),
      IsEmbedding e → ∀ f : C(X, D), ∃ g : C(Y, D), ∀ x, g (e x) = f x
