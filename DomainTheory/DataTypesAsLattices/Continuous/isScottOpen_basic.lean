module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega
public import DomainTheory.DataTypesAsLattices.Continuous.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


theorem isScottOpen_basic (n : ℕ) : IsScottOpen (basicNhhd n) :=
  ⟨{n}, by ext x; simp [basicNhhd]⟩

end DomainTheory.DataTypesAsLattices
