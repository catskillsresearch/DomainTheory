/-ai
The basic neighbourhood of the code 0 is the whole of Pω.

Extensionality and the fact that the finite set coded by 0 is empty give the equality.
ai-/
module

public import Mathlib.Topology.Bases
import all Mathlib.Topology.Bases
public import Mathlib.Topology.Order
import all Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega
public import DomainTheory.DataTypesAsLattices.Continuous.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace








theorem basicNhhd_zero : basicNhhd 0 = Set.univ := by
  ext x
  simp [basicNhhd, e_zero]

end DomainTheory.DataTypesAsLattices
