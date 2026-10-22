module

public import Mathlib.Order.CompleteLattice.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

section FixedPoints

variable {L : Type*} [CompleteLattice L]

/-- The fixed-point set `{x | e x = x}` of an endomap `e`, as a subtype. -/
abbrev IdemFix (e : L → L) : Type _ := {x : L // e x = x}

end FixedPoints

end DomainTheory.ContinuousLattice
