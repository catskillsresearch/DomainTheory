module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Topology.Inseparable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- `IsOpen` for `|𝒟|` is exactly Scott's condition (ii). -/
theorem isOpen_iff_isOpenFilter (U : Set V.Element) : IsOpen U ↔ V.OpenFilter U :=
  ⟨fun h => h, fun h => h⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
