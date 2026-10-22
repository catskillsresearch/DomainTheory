/-ai
A set U of elements of Pω is Scott open when U is the union of the basic neighbourhoods indexed by the members of some set of natural numbers.
ai-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega
public import DomainTheory.DataTypesAsLattices.Continuous.basicNhhd

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

/-- **Scott 1976, §1, Definition.** An open set is a union of basic neighbourhoods. -/
def IsScottOpen (U : Set Pomega) : Prop :=
  ∃ B : Set ℕ, U = ⋃ n ∈ B, basicNhhd n

end DomainTheory.DataTypesAsLattices
