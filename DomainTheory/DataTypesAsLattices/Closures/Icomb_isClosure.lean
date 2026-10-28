
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
public import DomainTheory.DataTypesAsLattices.Closures.Closure
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem Icomb_isClosure : Closure Icomb :=
  ⟨⟨subset_rfl, Icomb.isRetract⟩⟩

end DomainTheory.DataTypesAsLattices
