module

public import Mathlib.Data.Set.Basic
import all Mathlib.Data.Set.Basic
public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Element
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo_succ
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ext

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Antisymmetry of the filter-inclusion order. -/
theorem element_le_antisymm (x y : V.Element)
    (hxy : ∀ X, x.mem X → y.mem X) (hyx : ∀ X, y.mem X → x.mem X) :
    x = y :=
  @Element.ext α V x y fun X => ⟨hxy X, hyx X⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
