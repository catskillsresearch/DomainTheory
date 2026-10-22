module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem typed_of_arrowR {a b u : Pomega} (hu : typed u (arrowR a b)) :
    u = comp b (comp u a) := by
  simpa [typed, arrowR_app] using hu

end DomainTheory.DataTypesAsLattices
