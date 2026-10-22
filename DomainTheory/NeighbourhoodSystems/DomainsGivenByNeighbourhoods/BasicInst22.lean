/-ai
The elements of a neighbourhood system form a partial order under inclusion of the neighbourhoods they contain, Scott's approximation order.
ai-/
module

public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Element
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo_succ
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.element_le
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.element_le_refl
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.element_le_trans
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.element_le_antisymm

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Elements are ordered by inclusion of their membership predicates (Scott's approximation
order, Definition 1.8). -/
instance : PartialOrder V.Element where
  le := element_le V
  le_refl := element_le_refl V
  le_trans := element_le_trans V
  le_antisymm := element_le_antisymm V

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
