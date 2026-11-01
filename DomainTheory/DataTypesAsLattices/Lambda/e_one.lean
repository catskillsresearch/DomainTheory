module

public import DomainTheory.DataTypesAsLattices.Pomega.eDense

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem e_one : e 1 = ({0} : Pomega) := by
  simpa using e.pow2 0

end DomainTheory.DataTypesAsLattices
