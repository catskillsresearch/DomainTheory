module

public import DomainTheory.ContinuousLattice.Theorem212.completeLattice
public import DomainTheory.ContinuousLattice.Theorem212.idemFixRetraction
public import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_2_10_a
public import DomainTheory.ContinuousLattice.ScottMaps.preservesDirectedSup_monotone
public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

section FixedPoints

variable {L : Type*} [CompleteLattice L]


variable {e : L → L}


/-- **Fixed points of a Scott-continuous idempotent form a continuous lattice.** Combine the
retraction `idemFixRetraction` with Proposition 2.10(a). -/
theorem idemFix_isContinuousLattice (hidem : ∀ x, e (e x) = e x) (hsc : PreservesDirectedSup e)
    (hL : ContinuousLattice L) :
    @ContinuousLattice (IdemFix e)
      (IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)) := by
  let := IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)
  exact proposition_2_10_a (idemFixRetraction hidem hsc) hL

end FixedPoints
end DomainTheory.ContinuousLattice
