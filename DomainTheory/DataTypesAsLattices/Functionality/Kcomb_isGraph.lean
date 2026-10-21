/-ai
The K combinator equals the graph of its own application.

Extensionality of graphs, rewritten by the application equation for K.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Kcomb_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Kcomb_isGraph : Kcomb = graph (fun x => funOf Kcomb x) := by
  apply graph_ext
  intro x
  rw [Kcomb_app]

end DomainTheory.DataTypesAsLattices
