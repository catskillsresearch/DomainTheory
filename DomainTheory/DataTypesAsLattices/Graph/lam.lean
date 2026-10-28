
module

public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def lam (τ : Pomega → Pomega) : Pomega := graph τ

namespace lam

theorem eq_graph (τ : Pomega → Pomega) : lam τ = graph τ := rfl

end lam

end DomainTheory.DataTypesAsLattices
