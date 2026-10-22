module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.InS

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap

@[simp] theorem mem_concat {X Y : Set (List Bool)} {w : List Bool} :
    w ∈ concat X Y ↔ ∃ a ∈ X, ∃ b ∈ Y, a ++ b = w := Iff.rfl

end Exercise722

end DomainTheory.NeighbourhoodSystems
