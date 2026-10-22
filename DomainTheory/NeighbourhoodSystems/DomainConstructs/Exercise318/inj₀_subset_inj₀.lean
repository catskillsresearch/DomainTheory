/-ai
One left copy is contained in another if and only if the underlying set is contained in the other.

If the copies are nested and a token lies in the first set, its left tag lies in the first copy and hence in the second, so the token lies in the second set. Conversely, a token of the first copy is the left tag of some token of the first set, and inclusion of the sets puts that tag in the second copy.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₀
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

theorem inj₀_subset_inj₀ {X X' : Set α} :
    (inj₀ X : Set (Option (α ⊕ β))) ⊆ inj₀ X' ↔ X ⊆ X' := by
  constructor
  · intro h a ha; exact il_mem_inj₀.mp (h (il_mem_inj₀.mpr ha))
  · intro h t ht
    rw [inj₀, Set.mem_image] at ht
    obtain ⟨a, ha, rfl⟩ := ht
    exact il_mem_inj₀.mpr (h ha)

end DomainTheory.NeighbourhoodSystems
