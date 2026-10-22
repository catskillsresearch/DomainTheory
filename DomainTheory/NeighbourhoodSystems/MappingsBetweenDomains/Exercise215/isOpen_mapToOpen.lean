module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.mem_empty_iff_eq_top
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.mapToOpen

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

variable {γ : Type*} (V : NeighborhoodSystem γ)

/-- `mapToOpen f` is open: it is the preimage of the open point `{⊤} = [∅]` under the continuous
`x ↦ f(x)` (Exercise 2.13). -/
theorem isOpen_mapToOpen (f : ApproximableMap V O) : IsOpen (mapToOpen V f) := by
  have heq : mapToOpen V f = (fun x => f.toElementMap x) ⁻¹' O.basicOpen ∅ := by
    ext x
    simp only [mapToOpen, Set.mem_ofPred_eq, Set.mem_preimage, mem_basicOpen]
    exact (mem_empty_iff_eq_top (f.toElementMap x)).symm
  rw [heq]
  exact (O.isOpen_basicOpen ∅).preimage f.continuous_toElementMap

end DomainTheory.NeighbourhoodSystems.Exercise215
