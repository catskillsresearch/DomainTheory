module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₀

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

@[simp] theorem il_mem_inj₀ {X : Set α} {a : α} : (il a : Option (α ⊕ β)) ∈ inj₀ X ↔ a ∈ X := by
  simp only [inj₀, Set.mem_image, il]
  constructor
  · rintro ⟨a', ha', hb⟩; simp only [Option.some.injEq, Sum.inl.injEq] at hb; exact hb ▸ ha'
  · intro ha; exact ⟨a, ha, rfl⟩

end DomainTheory.NeighbourhoodSystems
