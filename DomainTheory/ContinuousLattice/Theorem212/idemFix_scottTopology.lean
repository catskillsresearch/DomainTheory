/-ai
The Scott topology of the fixed-point lattice of a Scott-continuous idempotent is the subspace topology induced by the inclusion from the Scott topology of the ambient lattice.

The fixed-point set is a retract of the ambient continuous lattice, and Proposition 2.10(b) identifies the Scott topology of such a retract with the induced topology.
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


/-- **Scott topology of the fixed-point lattice = subspace topology.** Proposition 2.10(b) applied
to `idemFixRetraction`: the Scott topology of `IdemFix e` is the topology induced by the inclusion
from the Scott topology of `L`. -/
theorem idemFix_scottTopology (hidem : ∀ x, e (e x) = e x) (hsc : PreservesDirectedSup e)
    (hL : ContinuousLattice L) :
    @scottTopologicalSpace (IdemFix e)
        (IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)) =
      TopologicalSpace.induced (Subtype.val : IdemFix e → L) scottTopologicalSpace := by
  let := IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)
  exact proposition_2_10_b (idemFixRetraction hidem hsc) hL

end FixedPoints
end DomainTheory.ContinuousLattice
