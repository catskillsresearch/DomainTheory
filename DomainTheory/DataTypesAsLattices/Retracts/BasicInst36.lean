module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import DomainTheory.DataTypesAsLattices.Retracts.fixpointsCompleteLattice

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

noncomputable instance fixpointsFunOfCompleteLattice (a : Pomega) :
    CompleteLattice (Fixpoints (funOf a)) :=
  fixpointsCompleteLattice (funOf_isScottContinuous a)

end DomainTheory.DataTypesAsLattices
