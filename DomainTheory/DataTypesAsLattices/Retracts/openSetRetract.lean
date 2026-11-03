module

public import DomainTheory.DataTypesAsLattices.Graph.graph

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def openSetRetract : Pomega :=
  graph (fun u => {m | ∃ n, e n ⊆ e m ∧ n ∈ u})

end DomainTheory.DataTypesAsLattices
