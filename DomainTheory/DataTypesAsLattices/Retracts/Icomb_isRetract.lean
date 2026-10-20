module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.Icomb_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





















theorem Icomb_isRetract : IsRetract Icomb := by
  change Icomb = graph (fun x => funOf Icomb (funOf Icomb x))
  have : (fun x => funOf Icomb (funOf Icomb x)) = fun x => x := by
    funext x
    simp [Icomb_app]
  rw [this]
  rfl

end DomainTheory.DataTypesAsLattices
