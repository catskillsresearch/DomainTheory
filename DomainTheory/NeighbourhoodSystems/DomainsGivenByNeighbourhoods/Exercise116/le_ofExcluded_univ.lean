module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem














/-- Every filter is `⊑ ofExcluded ℕ` (the whole family `𝒟`; every cofinite `Y` has `Yᶜ ⊆ ℕ`). -/
theorem le_ofExcluded_univ (x : cofiniteSystem.Element) :
    x ≤ ofExcluded Set.univ := by
  intro Y hY
  exact ⟨x.sub hY, Set.subset_univ _⟩

end Cofinite
end DomainTheory.NeighbourhoodSystems
