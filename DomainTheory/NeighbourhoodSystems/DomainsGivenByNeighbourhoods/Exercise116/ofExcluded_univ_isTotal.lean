/-ai
The filter of excluded points equal to the whole set of natural numbers is a total element of the cofinite system.

For any element, the comparison lemma places it below this filter, which is the totality condition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.le_ofExcluded_univ

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem


/-- **Exercise 1.16 — the unique total element.** `ofExcluded ℕ` (matching the greatest
element `ℕ ∈ 𝒫(ℕ)`) is total: it is `⊑`-maximal. -/
theorem ofExcluded_univ_isTotal : cofiniteSystem.IsTotal (ofExcluded Set.univ) :=
  fun y _ => le_ofExcluded_univ y

end Cofinite
end DomainTheory.NeighbourhoodSystems
