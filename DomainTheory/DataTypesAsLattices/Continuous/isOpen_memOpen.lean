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








theorem isOpen_memOpen (k : ℕ) : IsOpen (memOpen k) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨k, rfl⟩

end DomainTheory.DataTypesAsLattices
