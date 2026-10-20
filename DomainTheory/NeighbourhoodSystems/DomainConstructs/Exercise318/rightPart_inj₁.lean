module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_sumMaster
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_preimage_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_preimage_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.rightPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.mem_leftPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.mem_rightPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.leftPart_inj₀

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

@[simp] theorem rightPart_inj₁ (V₁ : NeighborhoodSystem β) (Y : Set β) :
    rightPart V₁ (inj₁ Y : Set (Option (α ⊕ β))) = Y := by
  ext b
  simp only [mem_rightPart, ir_mem_inj₁, il_mem_inj₁, none_mem_inj₁, exists_false, or_self,
    and_false]
  exact ⟨fun h => h.resolve_right (by simp), fun h => Or.inl h⟩

end DomainTheory.NeighbourhoodSystems
