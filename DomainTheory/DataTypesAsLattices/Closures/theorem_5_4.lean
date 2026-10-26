module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.boxTensor
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_boxTensor
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_boxPlus

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Theorem 5.4 (product half).** The boxed product of two
closures is a closure. -/
theorem theorem_5_4 {a b : Pomega} (ha : Closure a) (hb : Closure b) :
    Closure (boxTensor a b) :=
  ⟨⟨Icomb_subset_boxTensor ha hb, boxTensor.isRetract ha.out.2 hb.out.2⟩⟩

namespace theorem_5_4

/-- **Scott 1976, Theorem 5.4 (sum half).** If `a` and `b` are closure
operations then so is `a ⊞ b`. -/
theorem plus {a b : Pomega} (ha : Closure a) (hb : Closure b) :
    Closure (boxPlus a b) :=
  ⟨⟨Icomb_subset_boxPlus ha hb, boxPlus.isRetract ha.out.2 hb.out.2⟩⟩

end theorem_5_4

end DomainTheory.DataTypesAsLattices
