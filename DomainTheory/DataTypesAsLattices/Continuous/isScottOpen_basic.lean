/-ai
Every basic neighbourhood is Scott open.

The basic neighbourhood of n is the union of the family of basic neighbourhoods indexed by the singleton consisting of n.
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


theorem isScottOpen_basic (n : ℕ) : IsScottOpen (basicNhhd n) :=
  ⟨{n}, by ext x; simp [basicNhhd]⟩

end DomainTheory.DataTypesAsLattices
