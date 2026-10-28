module

public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_app

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem Scomb_isGraph : Scomb = graph (fun u => funOf Scomb u) := by
  apply graph_ext
  intro u
  rw [Scomb_app]

end DomainTheory.DataTypesAsLattices
