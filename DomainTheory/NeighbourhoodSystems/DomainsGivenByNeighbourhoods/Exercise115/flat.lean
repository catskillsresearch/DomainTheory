/-ai
The flat domain of Exercise 1.15 is the nested-or-disjoint neighbourhood system on the natural numbers whose neighbourhoods are the whole set together with the singletons. The master neighbourhood is the whole set, which is nonempty and is a neighbourhood. Nested-or-disjointness is the flat comparison lemma, and every neighbourhood is contained in the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.flatMem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.flatNOD

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Exercise 1.15 — the flat domain.** `𝒟 = {ℕ} ∪ {{n}}`. -/
def flat : NeighborhoodSystem ℕ :=
  ofNestedOrDisjoint flatMem Set.univ Set.univ_nonempty
    (Or.inl rfl) flatNOD (fun _ => Set.subset_univ _)

end DomainTheory.NeighbourhoodSystems.Exercise115
