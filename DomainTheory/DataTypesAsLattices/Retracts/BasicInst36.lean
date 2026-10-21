/-ai
The fixed-point set of the continuous map named by an element of Pω is given the complete lattice structure carried by the fixed points of a Scott-continuous endomap.
ai-/
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
