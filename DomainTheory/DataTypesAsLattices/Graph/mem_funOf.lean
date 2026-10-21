/-ai
A number m lies in the application of u to x if and only if some basic element contained in x has its code paired with m inside u.

The equivalence is the definitional membership clause.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Continuous
public import DomainTheory.DataTypesAsLattices.Graph.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem mem_funOf {u x : Pomega} {m : ℕ} :
    m ∈ funOf u x ↔ ∃ n, e n ⊆ x ∧ pair n m ∈ u := Iff.rfl

end DomainTheory.DataTypesAsLattices
