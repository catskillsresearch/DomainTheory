module

public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.condSet

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (2.7).** Conditional cases. -/
theorem eq_2_7_bot (x y : Pomega) : condSet botElem x y = botElem := by
  ext n
  simp [condSet, botElem]

end DomainTheory.DataTypesAsLattices
