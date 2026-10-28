module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.ContinuousLattices.completeLattice
public import DomainTheory.ContinuousLattice.ContinuousLattices.idemFixRetraction
public import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_2_10
public import DomainTheory.ContinuousLattice.ScottMaps.preservesDirectedSup_monotone
public import DomainTheory.ContinuousLattice.Specialization.scottTopologicalSpace
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

section FixedPoints

variable {L : Type*} [CompleteLattice L]

variable {e : L → L}

theorem idemFix_scottTopology (hidem : ∀ x, e (e x) = e x) (hsc : PreservesDirectedSup e)
    (hL : ContinuousLattice L) :
    @scottTopologicalSpace (IdemFix e)
        (IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)) =
      TopologicalSpace.induced (Subtype.val : IdemFix e → L) scottTopologicalSpace := by
  let := IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)
  exact proposition_2_10.b (idemFixRetraction hidem hsc) hL

end FixedPoints
end DomainTheory.ContinuousLattice
