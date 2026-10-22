module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

/-- Left tag `0a = some (inl a)`. -/
def il (a : α) : Option (α ⊕ β) := some (Sum.inl a)

end DomainTheory.NeighbourhoodSystems
