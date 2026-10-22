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

/-- Reflexivity of the filter-inclusion order. Named so Palomar can lock the
`PartialOrder` instance without a generated `._proof_N`. -/
theorem element_le_refl (x : V.Element) : ∀ X, x.mem X → x.mem X :=
  fun _ h => h

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
