/-ai
The right content of the sum master is the master of the second system.

Because the basepoint lies in the sum master, the membership criterion becomes the alternative of a right tag in the master or membership in the second master. A right tag in the master is neither the inserted basepoint nor a left tag, so it lies in the right copy of the second master and the token lies in that master. The other direction uses the master clause.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.sumMaster
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_sumMaster
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_preimage_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_preimage_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.rightPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.mem_leftPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.mem_rightPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.leftPart_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.rightPart_inj₁

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

theorem rightPart_sumMaster (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    rightPart V₁ (sumMaster V₀ V₁) = V₁.master := by
  ext b
  simp only [mem_rightPart, none_mem_sumMaster, or_true, and_true]
  constructor
  · rintro (h | h)
    · have : (ir b : Option (α ⊕ β)) ∈ sumMaster V₀ V₁ := h
      rcases Set.mem_insert_iff.mp this with h' | h'
      · exact absurd h' (by simp [ir])
      · rcases h' with h'' | h''
        · exact absurd h'' (by simp)
        · exact (ir_mem_inj₁).mp h''
    · exact h
  · intro hb; exact Or.inr hb

end DomainTheory.NeighbourhoodSystems
