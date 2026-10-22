module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_inj₁

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

theorem inj₁_subset_inj₁ {Y Y' : Set β} :
    (inj₁ Y : Set (Option (α ⊕ β))) ⊆ inj₁ Y' ↔ Y ⊆ Y' := by
  constructor
  · intro h b hb; exact ir_mem_inj₁.mp (h (ir_mem_inj₁.mpr hb))
  · intro h t ht
    rw [inj₁, Set.mem_image] at ht
    obtain ⟨b, hb, rfl⟩ := ht
    exact ir_mem_inj₁.mpr (h hb)

end DomainTheory.NeighbourhoodSystems
