module

public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem graph_funOf_ext {f g : Pomega}
    (hf : f = graph (fun x => funOf f x))
    (hg : g = graph (fun x => funOf g x))
    (h : ∀ x, funOf f x = funOf g x) : f = g := by
  rw [hf, hg]
  exact graph_ext h

end DomainTheory.DataTypesAsLattices
