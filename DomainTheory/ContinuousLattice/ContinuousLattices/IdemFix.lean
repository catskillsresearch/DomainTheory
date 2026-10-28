module

public import Mathlib.Order.CompleteLattice.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

section FixedPoints

variable {L : Type*} [CompleteLattice L]

abbrev IdemFix (e : L → L) : Type _ := {x : L // e x = x}

end FixedPoints

end DomainTheory.ContinuousLattice
