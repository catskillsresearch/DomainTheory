module

public import DomainTheory.DataTypesAsLattices.Continuous.Basic
import Mathlib.Tactic.Bound.Init

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

theorem isOpen_memOpen (k : ℕ) : IsOpen (memOpen k) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨k, rfl⟩

end DomainTheory.DataTypesAsLattices
