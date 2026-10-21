/-ai
The basepoint does not lie in a left copy.

A supposed membership equates a left tag with the basepoint, and simplification of the left tag rejects that equality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_mem_inj₀

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

@[simp] theorem none_mem_inj₀ {X : Set α} : (none : Option (α ⊕ β)) ∉ inj₀ X := by
  rintro ⟨a, _, hb⟩; exact absurd hb (by simp [il])

end DomainTheory.NeighbourhoodSystems
