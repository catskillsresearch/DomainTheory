module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.comp_app
public import DomainTheory.DataTypesAsLattices.Retracts.IsRetract
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

theorem retract_app {a : Pomega} (ha : IsRetract a) (x : Pomega) :
    funOf a (funOf a x) = funOf a x := by
  have := congrArg (fun u => funOf u x) ha
  simpa [comp_app] using this.symm

end DomainTheory.DataTypesAsLattices
