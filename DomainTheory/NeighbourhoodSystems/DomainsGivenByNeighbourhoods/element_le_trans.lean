module

public import Mathlib.Data.Set.Basic
import all Mathlib.Data.Set.Basic
public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Element
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo_succ

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Transitivity of the filter-inclusion order. -/
theorem element_le_trans (x y z : V.Element)
    (hxy : ∀ X, x.mem X → y.mem X) (hyz : ∀ X, y.mem X → z.mem X) :
    ∀ X, x.mem X → z.mem X :=
  fun X h => hyz X (hxy X h)

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
