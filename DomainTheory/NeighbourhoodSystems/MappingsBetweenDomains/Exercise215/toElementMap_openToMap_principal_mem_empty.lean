module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_mem_empty
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.openToMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

variable {γ : Type*} (V : NeighborhoodSystem γ)

/-- The value of `openToMap U hU` on the finite element `↑X` contains `∅` iff `↑X ∈ U`; i.e.
`(openToMap U hU)(↑X) = ⊤ ↔ ↑X ∈ U`. -/
theorem toElementMap_openToMap_principal_mem_empty (U : Set V.Element) (hU : IsOpen U)
    {X : Set γ} (hX : V.mem X) :
    ((openToMap V U hU).toElementMap (V.principal hX)).mem ∅ ↔ V.principal hX ∈ U := by
  rw [← (openToMap V U hU).rel_iff_mem_principal hX]
  constructor
  · rintro ⟨_, _, fimpl⟩
    obtain ⟨_, hmem⟩ := fimpl rfl
    exact hmem
  · intro h
    exact ⟨hX, O_mem_empty, fun _ => ⟨hX, h⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise215
