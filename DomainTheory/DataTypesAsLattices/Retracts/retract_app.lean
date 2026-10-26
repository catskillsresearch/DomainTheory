module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.Retract

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem retract_app {a : Pomega} (ha : Retract a) (x : Pomega) :
    funOf a (funOf a x) = funOf a x := by
  have := congrArg (fun u => funOf u x) ha.out
  simpa [comp.app] using this.symm

end DomainTheory.DataTypesAsLattices
