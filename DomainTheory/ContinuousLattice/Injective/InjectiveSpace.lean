module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Maps.Basic

@[expose] public section

open Topology TopologicalSpace

universe u v

class InjectiveSpace (D : Type v) [TopologicalSpace D] : Prop where
  extension :
    ∀ {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (e : X → Y),
      IsEmbedding e → ∀ f : C(X, D), ∃ g : C(Y, D), ∀ x, g (e x) = f x
