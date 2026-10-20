module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

/-- The tagged right copy `1Y = {some (inr b) ∣ b ∈ Y}`. -/
def inj₁ (Y : Set β) : Set (Option (α ⊕ β)) := ir '' Y

end DomainTheory.NeighbourhoodSystems
