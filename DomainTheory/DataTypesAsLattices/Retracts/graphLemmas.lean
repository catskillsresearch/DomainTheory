module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem graph_ext {f g : Pomega → Pomega} (h : ∀ x, f x = g x) :
    graph f = graph g := by
  simp [graph, h]

theorem graph_const_bot : graph (fun _ => botElem) = botElem := by
  ext p
  simp [graph, botElem]

end DomainTheory.DataTypesAsLattices
