/-ai
Scott's product theorem says that the boxed product of two closures is a closure.

The identity combinator is contained in the boxed product, and the boxed product of the underlying retracts is a retract.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.boxTensor_isRetract
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_boxTensor

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 5.4 (product half).** The boxed product of two
closures is a closure. -/
theorem theorem_5_4 {a b : Pomega} (ha : Closure a) (hb : Closure b) :
    Closure (boxTensor a b) :=
  ⟨⟨Icomb_subset_boxTensor ha hb, boxTensor_isRetract ha.out.2 hb.out.2⟩⟩

end DomainTheory.DataTypesAsLattices
