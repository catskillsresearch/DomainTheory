module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice

@[expose] public section


namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]


/-- In a continuous lattice, `y` is the actual supremum of `{x | x ≪ y}`. -/
theorem sSup_wayBelow (h : ContinuousLattice D) (y : D) :
    sSup {x | x ≪ y} = y :=
  (h.out y).sSup_eq

end DomainTheory.ContinuousLattice
