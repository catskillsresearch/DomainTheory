module

public import DomainTheory.ContinuousLattice.Constructions
public import DomainTheory.ContinuousLattice.FunctionSpaces
public import DomainTheory.ContinuousLattice.Theorem212.IdemFix
public import DomainTheory.ContinuousLattice.Theorem212.completeLattice

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

open Topology Set

section FixedPoints

variable {L : Type*} [CompleteLattice L]

namespace IdemFix

variable {e : L → L}

/-- The ambient supremum corrected by `e` is the supremum in `IdemFix e`. -/
theorem coe_sSup (hidem : ∀ x, e (e x) = e x) (hmono : Monotone e) (S : Set (IdemFix e)) :
    letI := completeLattice hidem hmono
    ((sSup S : IdemFix e) : L) = e (sSup (Subtype.val '' S)) := rfl

end IdemFix

end FixedPoints

end DomainTheory.ContinuousLattice
