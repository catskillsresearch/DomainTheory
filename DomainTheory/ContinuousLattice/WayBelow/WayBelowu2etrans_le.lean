module

public import DomainTheory.ContinuousLattice.WayBelow.WayBelow

@[expose] public section


namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]


/-- **Scott 1972, Proposition 2.2(iii).** `x ≪ y` and `y ≤ z` imply `x ≪ z` (monotone on the
right). -/
theorem WayBelow.trans_le {x y z : D} (h : x ≪ y) (hyz : y ≤ z) : x ≪ z := by
  obtain ⟨U, hU, hyU, hsub⟩ := h
  exact ⟨U, hU, hU.1 hyz hyU, hsub⟩

end DomainTheory.ContinuousLattice
