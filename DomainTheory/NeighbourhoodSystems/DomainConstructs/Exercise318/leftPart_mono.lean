/-ai
The left content is monotone in the sum set.

Rewrite membership by the left-content criterion. Inclusion sends a left tag of the smaller set into the larger set, and it sends a right tag or the basepoint of the smaller set into the larger set while leaving membership in the first master unchanged.
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
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.leftPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.mem_leftPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.mem_rightPart

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

theorem leftPart_mono (V₀ : NeighborhoodSystem α) {W W' : Set (Option (α ⊕ β))} (h : W ⊆ W') :
    leftPart V₀ W ⊆ leftPart V₀ W' := by
  intro a ha
  rw [mem_leftPart] at ha ⊢
  exact ha.imp (fun h' => h h') (fun ⟨hm, hc⟩ => ⟨hm, hc.imp (fun ⟨b, hb⟩ => ⟨b, h hb⟩) (fun hn => h hn)⟩)

end DomainTheory.NeighbourhoodSystems
