module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Topology.Inseparable
import all Mathlib.Topology.Inseparable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122.isOpen_basicOpen
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122.isOpen_isUpperSet

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)







/-- **Exercise 1.22, condition (iii).** The approximation order is recovered from the topology:
`x ⊑ y` iff every open set containing `x` also contains `y`.

* `→` is upward closure of opens (`isOpen_isUpperSet`);
* `←` tests against the open basic neighbourhood `[X]` for each `X ∈ x`. -/
theorem le_iff_isOpen_imp (x y : V.Element) :
    x ≤ y ↔ ∀ U : Set V.Element, IsOpen U → x ∈ U → y ∈ U := by
  constructor
  · intro hxy U hU hxU
    exact V.isOpen_isUpperSet hU hxU hxy
  · intro h
    exact fun X hX => h (V.basicOpen X) (V.isOpen_basicOpen X) hX

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
