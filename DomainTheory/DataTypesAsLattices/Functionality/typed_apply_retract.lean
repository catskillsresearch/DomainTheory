
module

public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.retract_app
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem typed_apply_retract {a x : Pomega} (ha : Retract a) :
    typed (funOf a x) a :=
  (retract_app ha x).symm

end DomainTheory.DataTypesAsLattices
