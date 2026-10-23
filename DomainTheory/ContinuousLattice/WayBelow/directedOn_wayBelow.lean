module

public import DomainTheory.ContinuousLattice.WayBelow.WayBelow

@[expose] public section


namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]


/-- The set `{x | x ≪ y}` of elements way below `y` is directed: it is closed under binary
joins by Proposition 2.2(ii) (`WayBelow.sup`). This holds in *any* complete lattice. -/
theorem directedOn_wayBelow (y : D) : DirectedOn (· ≤ ·) {x | x ≪ y} :=
  fun a ha b hb => ⟨a ⊔ b, ha.sup hb, le_sup_left, le_sup_right⟩

end DomainTheory.ContinuousLattice
