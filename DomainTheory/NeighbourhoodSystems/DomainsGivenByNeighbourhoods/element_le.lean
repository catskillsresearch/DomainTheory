/-ai
The approximation order on elements is filter inclusion: one element is below another when every neighbourhood of the first is a neighbourhood of the second.
ai-/
module

public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Element
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo_succ

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Filter-inclusion order on elements (Scott's approximation order, Definition 1.8).
Named so Palomar can lock the `PartialOrder` relation without inlining it. -/
def element_le (x y : V.Element) : Prop :=
  ∀ X, x.mem X → y.mem X

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
