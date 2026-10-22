module

public import DomainTheory.ContinuousLattice.Theorem212.completeLattice
public import DomainTheory.ContinuousLattice.Theorem212.idemFix_retr_preservesDirectedSup
public import DomainTheory.ContinuousLattice.Theorem212.idemFix_incl_preservesDirectedSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeRetraction
public import DomainTheory.ContinuousLattice.ScottMaps.continuous_of_preservesDirectedSup
public import DomainTheory.ContinuousLattice.ScottMaps.preservesDirectedSup_monotone
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

section FixedPoints

variable {L : Type*} [CompleteLattice L]

variable {e : L → L}

/-- The fixed-point set of a Scott-continuous idempotent `e` on `L`, with the
ambient-supremum-corrected complete-lattice structure, is a *retract of `L`*: the inclusion and the
corestriction of `e` are Scott-continuous and compose to the identity. -/
noncomputable def idemFixRetraction (hidem : ∀ x, e (e x) = e x) (hsc : PreservesDirectedSup e) :
    @IsContinuousLatticeRetraction (IdemFix e) L
      (IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)) _ :=
  letI := IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)
  { incl := ⟨Subtype.val,
      continuous_of_preservesDirectedSup (idemFix_incl_preservesDirectedSup hidem hsc)⟩
    retr := ⟨fun x => ⟨e x, hidem x⟩,
      continuous_of_preservesDirectedSup (idemFix_retr_preservesDirectedSup hidem hsc)⟩
    retr_incl := fun k => Subtype.ext k.2 }

end FixedPoints

end DomainTheory.ContinuousLattice
