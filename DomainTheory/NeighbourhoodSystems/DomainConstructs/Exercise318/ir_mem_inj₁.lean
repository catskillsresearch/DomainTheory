module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_inj₀

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

@[simp] theorem ir_mem_inj₁ {Y : Set β} {b : β} : (ir b : Option (α ⊕ β)) ∈ inj₁ Y ↔ b ∈ Y := by
  simp only [inj₁, Set.mem_image, ir]
  constructor
  · rintro ⟨b', hb', hb⟩; simp only [Option.some.injEq, Sum.inr.injEq] at hb; exact hb ▸ hb'
  · intro hb; exact ⟨b, hb, rfl⟩

end DomainTheory.NeighbourhoodSystems
