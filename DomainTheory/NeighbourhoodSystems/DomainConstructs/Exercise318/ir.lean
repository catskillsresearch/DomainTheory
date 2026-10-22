module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

/-- Right tag `1b = some (inr b)`. -/
def ir (b : β) : Option (α ⊕ β) := some (Sum.inr b)

end DomainTheory.NeighbourhoodSystems
