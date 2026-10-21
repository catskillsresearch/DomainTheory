/-ai
The S combinator equals the graph of its own application.

Extensionality of graphs, rewritten by the application equation for S.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






















theorem Scomb_isGraph : Scomb = graph (fun u => funOf Scomb u) := by
  apply graph_ext
  intro u
  rw [Scomb_app]

end DomainTheory.DataTypesAsLattices
