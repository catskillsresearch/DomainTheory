module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.InS
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.mem_concat

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap

/-- The concatenation of two non-empty languages is non-empty. -/
theorem concat_nonempty {X Y : Set (List Bool)} (hX : X.Nonempty) (hY : Y.Nonempty) :
    (concat X Y).Nonempty := by
  obtain ⟨a, ha⟩ := hX
  obtain ⟨b, hb⟩ := hY
  exact ⟨a ++ b, a, ha, b, hb, rfl⟩

end Exercise722

end DomainTheory.NeighbourhoodSystems
