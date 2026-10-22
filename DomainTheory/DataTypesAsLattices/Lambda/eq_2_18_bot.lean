module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (2.18).** Constants as graphs of constant maps. -/
theorem eq_2_18_bot : botElem = graph (fun _ => botElem) := by
  ext p
  constructor
  · intro hp; exact hp.elim
  · intro hp
    rcases hp with ⟨_, _, _, hm⟩
    simp [botElem] at hm

end DomainTheory.DataTypesAsLattices
