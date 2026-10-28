module

public import DomainTheory.ContinuousLattice.Injective.InjectiveSpace
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open Topology TopologicalSpace

universe v

theorem proposition_1_4 {D : Type v} {D' : Type v} [TopologicalSpace D] [TopologicalSpace D']
    (hD : InjectiveSpace.{u} D) (s : C(D', D)) (r : C(D, D')) (hrs : ∀ d, r (s d) = d) :
    InjectiveSpace.{u} D' :=
  InjectiveSpace.of_retract hD s r hrs
