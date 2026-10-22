module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem topElem_ne_botElem : (topElem : Pomega) ≠ botElem := by
  intro h
  have h0 : (0 : ℕ) ∈ (botElem : Pomega) := h ▸ Set.mem_univ 0
  simp [botElem] at h0

end DomainTheory.DataTypesAsLattices
