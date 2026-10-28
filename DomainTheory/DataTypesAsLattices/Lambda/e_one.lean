module

public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem e_one : e 1 = ({0} : Pomega) := by
  simpa using e_pow2 0

end DomainTheory.DataTypesAsLattices
