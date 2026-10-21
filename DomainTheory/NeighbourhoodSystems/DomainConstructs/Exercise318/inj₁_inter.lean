/-ai
The intersection of two right copies is the right copy of the intersection.

Extensionality reduces the claim to an arbitrary sum token. For the basepoint, a left tag, and a right tag, simplification of intersection membership, the right tag, and the right copy makes the two sides agree.
ai-/
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
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_inj₁

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

theorem inj₁_inter (Y Y' : Set β) :
    (inj₁ Y ∩ inj₁ Y' : Set (Option (α ⊕ β))) = inj₁ (Y ∩ Y') := by
  ext t; rcases t with _ | (a | b) <;>
    simp [Set.mem_inter_iff, ir, inj₁]

end DomainTheory.NeighbourhoodSystems
