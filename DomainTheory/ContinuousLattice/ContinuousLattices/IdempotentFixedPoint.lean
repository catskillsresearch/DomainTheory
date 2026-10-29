module

public import Mathlib.Order.CompleteLattice.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

variable {L : Type*} [CompleteLattice L]

/-- Fixed points `{x | e x = x}` of an endomap on a complete lattice. -/
abbrev IdempotentFixedPoint (e : L → L) : Type _ := {x : L // e x = x}

end DomainTheory.ContinuousLattice
