module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem minExtend_bot (p : ℕ → Pomega) : minExtend p botElem = botElem := by
  simp [minExtend, botElem]

end DomainTheory.DataTypesAsLattices
