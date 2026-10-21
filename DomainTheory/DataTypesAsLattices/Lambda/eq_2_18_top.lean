/-ai
Top is the graph of the constant map with value ⊤.

Every number is some pair code, and the constant value contains its right component. Every element of a graph lies in ⊤.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem eq_2_18_top : topElem = graph (fun _ => topElem) := by
  ext p
  constructor
  · intro _
    obtain ⟨n, m, rfl⟩ := exists_pair p
    exact ⟨n, m, rfl, Set.mem_univ m⟩
  · intro; trivial

end DomainTheory.DataTypesAsLattices
