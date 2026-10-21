/-ai
The fixed points of a Scott-continuous idempotent on a continuous lattice form a continuous lattice.

The fixed-point set is a retract of the ambient lattice, and Proposition 2.10(a) says that a retract of a continuous lattice is a continuous lattice.
ai-/
module

public import DomainTheory.ContinuousLattice.Constructions
public import DomainTheory.ContinuousLattice.FunctionSpaces
public import DomainTheory.ContinuousLattice.Theorem212.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

section FixedPoints

variable {L : Type*} [CompleteLattice L]


variable {e : L → L}


/-- **Fixed points of a Scott-continuous idempotent form a continuous lattice.** Combine the
retraction `idemFixRetraction` with Proposition 2.10(a). -/
theorem idemFix_isContinuousLattice (hidem : ∀ x, e (e x) = e x) (hsc : PreservesDirectedSup e)
    (hL : IsContinuousLattice L) :
    @IsContinuousLattice (IdemFix e)
      (IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)) := by
  let := IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)
  exact proposition_2_10_a (idemFixRetraction hidem hsc) hL

end FixedPoints
end DomainTheory.ContinuousLattice
