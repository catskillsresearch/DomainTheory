module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.openR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices



































theorem openR_expansive (u : Pomega) : u ⊆ funOf openR u := by
  intro k hk
  rw [openR_app]
  exact ⟨k, subset_rfl, hk⟩

end DomainTheory.DataTypesAsLattices
