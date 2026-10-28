module

public import Mathlib.Topology.Bases
public import DomainTheory.DataTypesAsLattices.Continuous.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.memOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

theorem isOpen_memOpen (k : ℕ) : IsOpen (memOpen k) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨k, rfl⟩

end DomainTheory.DataTypesAsLattices
