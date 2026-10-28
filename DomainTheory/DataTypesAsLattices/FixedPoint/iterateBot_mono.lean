module

public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.FixedPoint.iterateBot
public import DomainTheory.DataTypesAsLattices.FixedPoint.fix

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem iterateBot_mono {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    ∀ n, iterateBot f n ⊆ iterateBot f (n + 1)
  | 0 => by
    simp [iterateBot, botElem]
  | n + 1 =>
    IsScottContinuous.monotone hf (iterateBot_mono hf n)

end DomainTheory.DataTypesAsLattices
