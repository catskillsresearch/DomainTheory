/-ai
The right content is monotone in the sum set.

Rewrite membership by the right-content criterion. Inclusion sends a right tag of the smaller set into the larger set, and it sends a left tag or the basepoint of the smaller set into the larger set while leaving membership in the second master unchanged.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
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

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

theorem rightPart_mono (V₁ : NeighborhoodSystem β) {W W' : Set (Option (α ⊕ β))} (h : W ⊆ W') :
    rightPart V₁ W ⊆ rightPart V₁ W' := by
  intro b hb
  rw [mem_rightPart] at hb ⊢
  exact hb.imp (fun h' => h h') (fun ⟨hm, hc⟩ => ⟨hm, hc.imp (fun ⟨a, ha⟩ => ⟨a, h ha⟩) (fun hn => h hn)⟩)

end DomainTheory.NeighbourhoodSystems
