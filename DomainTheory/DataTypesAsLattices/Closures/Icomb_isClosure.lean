
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Icomb_isClosure : Closure Icomb :=
  ⟨⟨subset_rfl, Icomb_isRetract⟩⟩

end DomainTheory.DataTypesAsLattices
