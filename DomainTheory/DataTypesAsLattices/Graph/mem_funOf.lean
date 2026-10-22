
module

public import DomainTheory.DataTypesAsLattices.Continuous
public import DomainTheory.DataTypesAsLattices.Graph.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem mem_funOf {u x : Pomega} {m : ℕ} :
    m ∈ funOf u x ↔ ∃ n, e n ⊆ x ∧ pair n m ∈ u := Iff.rfl

end DomainTheory.DataTypesAsLattices
