module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def openR : Pomega :=
  graph (fun u => {m | ∃ n, e n ⊆ e m ∧ n ∈ u})

end DomainTheory.DataTypesAsLattices
