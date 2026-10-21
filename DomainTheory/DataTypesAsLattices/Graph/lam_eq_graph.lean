/-ai
Abstraction of tau equals the graph of tau.

The two sides are definitionally identical.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Continuous
public import DomainTheory.DataTypesAsLattices.Graph.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






theorem lam_eq_graph (τ : Pomega → Pomega) : lam τ = graph τ := rfl

end DomainTheory.DataTypesAsLattices
