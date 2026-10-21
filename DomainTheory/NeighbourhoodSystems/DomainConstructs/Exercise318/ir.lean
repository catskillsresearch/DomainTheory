/-ai
The right tag of a token is the sum token formed by applying the option constructor to the right injection of that token into the disjoint sum.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

/-- Right tag `1b = some (inr b)`. -/
def ir (b : β) : Option (α ⊕ β) := some (Sum.inr b)

end DomainTheory.NeighbourhoodSystems
