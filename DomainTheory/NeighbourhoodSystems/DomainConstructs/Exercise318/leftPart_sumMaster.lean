/-ai
The left content of the sum master is the master of the first system.

Because the basepoint lies in the sum master, the membership criterion becomes the alternative of a left tag in the master or membership in the first master. A left tag in the master is neither the inserted basepoint nor a right tag, so it lies in the left copy of the first master and the token lies in that master. The other direction uses the master clause.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il
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
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.leftPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.mem_leftPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.mem_rightPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.leftPart_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.rightPart_inj₁

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

theorem leftPart_sumMaster (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    leftPart V₀ (sumMaster V₀ V₁) = V₀.master := by
  ext a
  simp only [mem_leftPart, none_mem_sumMaster, or_true, and_true]
  constructor
  · rintro (h | h)
    · have : (il a : Option (α ⊕ β)) ∈ sumMaster V₀ V₁ := h
      rcases Set.mem_insert_iff.mp this with h' | h'
      · exact absurd h' (by simp [il])
      · rcases h' with h'' | h''
        · exact (il_mem_inj₀).mp h''
        · exact absurd h'' (by simp)
    · exact h
  · intro ha; exact Or.inr ha

end DomainTheory.NeighbourhoodSystems
