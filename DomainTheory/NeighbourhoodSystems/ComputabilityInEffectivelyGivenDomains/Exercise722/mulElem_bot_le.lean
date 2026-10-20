module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Ssys_master

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap




























/-- **`⊥` is a left-annihilator up to `≤`**: `⊥·y ≤ y`. (`⊥`'s only neighbourhood is `Δ = Σ`, and
`Y ⊆ Σ·Y` via the empty-word split, so any witness collapses onto `y` itself.) -/
theorem mulElem_bot_le (y : Ssys.Element) : mulElem Ssys.bot y ≤ y := by
  rintro Z ⟨hInS, X, hX, Y, hY, hsub⟩
  rw [NeighborhoodSystem.mem_bot, Ssys_master] at hX
  subst hX
  refine y.up_mem hY hInS fun w hw => hsub ?_
  simpa using append_mem_concat (Set.mem_univ ([] : List Bool)) hw

end Exercise722
end DomainTheory.NeighbourhoodSystems
