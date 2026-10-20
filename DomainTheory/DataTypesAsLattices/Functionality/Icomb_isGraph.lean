module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






















theorem Icomb_isGraph : Icomb = graph (fun x => funOf Icomb x) := by
  apply graph_ext
  intro x
  rw [Icomb_app]

end DomainTheory.DataTypesAsLattices
