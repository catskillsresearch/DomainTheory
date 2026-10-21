/-ai
The left copy of a set of tokens is the image of that set under the left tag.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

/-- The tagged left copy `0X = {some (inl a) ∣ a ∈ X}`. -/
def inj₀ (X : Set α) : Set (Option (α ⊕ β)) := il '' X

end DomainTheory.NeighbourhoodSystems
