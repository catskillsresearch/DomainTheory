module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- Isolated points of a closure are its values on finite sets, and
conversely every `a(e n)` is a typed point. -/
theorem theorem_5_1_isolated {a : Pomega} (_ha : Closure a) {x : Pomega}
    (hx : typed x a) :
    Isolated x → ∃ n, x = funOf a (e n) := by
  intro h
  obtain ⟨n, hn⟩ := h.out
  refine ⟨n, ?_⟩
  rw [hn] at hx ⊢
  exact hx

end DomainTheory.DataTypesAsLattices
