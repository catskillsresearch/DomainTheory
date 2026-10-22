
module

public import DomainTheory.DataTypesAsLattices.Continuous
public import DomainTheory.DataTypesAsLattices.Graph.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem mem_graph {f : Pomega → Pomega} {p : ℕ} :
    p ∈ graph f ↔ ∃ n m, p = pair n m ∧ m ∈ f (e n) := Iff.rfl

end DomainTheory.DataTypesAsLattices
