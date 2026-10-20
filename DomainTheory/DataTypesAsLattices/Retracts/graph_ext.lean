module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






































theorem graph_ext {f g : Pomega → Pomega} (h : ∀ x, f x = g x) :
    graph f = graph g := by
  simp [graph, h]

end DomainTheory.DataTypesAsLattices
