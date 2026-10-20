module

public import DomainTheory.ContinuousLattice.Constructions
public import DomainTheory.ContinuousLattice.FunctionSpaces
public import DomainTheory.ContinuousLattice.Theorem212.IdemFix
public import DomainTheory.ContinuousLattice.Theorem212.supSet
public import DomainTheory.ContinuousLattice.Theorem212.isLUB_sSup

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

open Topology Set

section FixedPoints

variable {L : Type*} [CompleteLattice L]

namespace IdemFix

variable {e : L → L}

@[reducible] noncomputable def completeLattice (hidem : ∀ x, e (e x) = e x) (hmono : Monotone e) :
    CompleteLattice (IdemFix e) :=
  letI := supSet hidem
  completeLatticeOfSup (IdemFix e) (isLUB_sSup hidem hmono)

end IdemFix

end FixedPoints

end DomainTheory.ContinuousLattice
