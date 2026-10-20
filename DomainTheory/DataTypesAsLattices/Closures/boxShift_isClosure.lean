module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.boxShift_isRetract
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_boxShift

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































theorem boxShift_isClosure {a : Pomega} (ha : IsClosure a) :
    IsClosure (boxShift a) :=
  ⟨Icomb_subset_boxShift ha, boxShift_isRetract ha.2⟩

end DomainTheory.DataTypesAsLattices
