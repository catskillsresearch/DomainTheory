module

public import DomainTheory.ContinuousLattice.ContinuousLattices.completeLattice
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

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
