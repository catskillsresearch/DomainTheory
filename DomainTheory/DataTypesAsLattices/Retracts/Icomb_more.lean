module

public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace Icomb

theorem isRetract : Retract Icomb := by
  constructor
  change Icomb = graph (fun x => funOf Icomb (funOf Icomb x))
  have : (fun x => funOf Icomb (funOf Icomb x)) = fun x => x := by
    funext x
    simp [app]
  rw [this]
  rfl

end Icomb

end DomainTheory.DataTypesAsLattices
