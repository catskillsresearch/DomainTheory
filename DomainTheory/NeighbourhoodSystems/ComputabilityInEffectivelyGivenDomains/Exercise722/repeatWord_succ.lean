/-ai
The repetition of a word of successor count is the word followed by the repetition of the previous count.

This is the successor clause of the definition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap































theorem repeatWord_succ (w : List Bool) (n : ℕ) :
    repeatWord w (n + 1) = w ++ repeatWord w n := rfl

end Exercise722
end DomainTheory.NeighbourhoodSystems
