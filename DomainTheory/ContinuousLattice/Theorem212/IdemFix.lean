/-ai
The fixed-point set of an endomap is the subtype of elements that the endomap leaves unchanged.
ai-/
module

public import DomainTheory.ContinuousLattice.Constructions
public import DomainTheory.ContinuousLattice.FunctionSpaces

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

open Topology Set

section FixedPoints

variable {L : Type*} [CompleteLattice L]

/-- The fixed-point set `{x | e x = x}` of an endomap `e`, as a subtype. -/
abbrev IdemFix (e : L → L) : Type _ := {x : L // e x = x}

end FixedPoints

end DomainTheory.ContinuousLattice
