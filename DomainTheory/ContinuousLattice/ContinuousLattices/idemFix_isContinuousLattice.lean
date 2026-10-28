module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.ContinuousLattices.completeLattice
public import DomainTheory.ContinuousLattice.ContinuousLattices.idemFixRetraction
public import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_2_10
public import DomainTheory.ContinuousLattice.ScottMaps.preservesDirectedSup_monotone
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

section FixedPoints

variable {L : Type*} [CompleteLattice L]

variable {e : L → L}

theorem idemFix_isContinuousLattice (hidem : ∀ x, e (e x) = e x) (hsc : PreservesDirectedSup e)
    (hL : ContinuousLattice L) :
    @ContinuousLattice (IdemFix e)
      (IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)) := by
  let := IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)
  exact proposition_2_10.a (idemFixRetraction hidem hsc) hL

end FixedPoints
end DomainTheory.ContinuousLattice
