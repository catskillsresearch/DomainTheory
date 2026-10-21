/-ai
A code p lies in the graph of f if and only if p is a pair of n and m with m in f at the basic element coded by n.

The equivalence is the definitional membership clause.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Continuous
public import DomainTheory.DataTypesAsLattices.Graph.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem mem_graph {f : Pomega → Pomega} {p : ℕ} :
    p ∈ graph f ↔ ∃ n m, p = pair n m ∧ m ∈ f (e n) := Iff.rfl

end DomainTheory.DataTypesAsLattices
