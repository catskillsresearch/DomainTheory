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
