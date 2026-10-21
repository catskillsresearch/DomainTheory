/-ai
The concatenation of two languages is the set of words that split as a word of the first language followed by a word of the second.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap

/-- Scott's `XY = {στ ∣ σ ∈ X and τ ∈ Y}`: the concatenation of two languages. -/
def concat (X Y : Set (List Bool)) : Set (List Bool) := {w | ∃ a ∈ X, ∃ b ∈ Y, a ++ b = w}

end Exercise722
end DomainTheory.NeighbourhoodSystems
