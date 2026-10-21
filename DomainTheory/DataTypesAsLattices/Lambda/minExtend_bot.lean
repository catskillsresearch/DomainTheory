/-ai
The minimal extension of any sequence at the bottom element is the bottom element.

The equality is the definitions of the minimal extension and the bottom element.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices




theorem minExtend_bot (p : ℕ → Pomega) : minExtend p botElem = botElem := by
  simp [minExtend, botElem]

end DomainTheory.DataTypesAsLattices
