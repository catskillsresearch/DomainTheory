module

public import Mathlib.Topology.Bases
public import DomainTheory.DataTypesAsLattices.Continuous.basicNhhd
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def IsScottOpen (U : Set Pomega) : Prop :=
  ∃ B : Set ℕ, U = ⋃ n ∈ B, basicNhhd n

end DomainTheory.DataTypesAsLattices
