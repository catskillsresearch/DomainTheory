/-ai
The stem domain of Exercise 1.15 is the nested-or-disjoint neighbourhood system on the natural numbers whose neighbourhoods are the whole set, the pair {0, 1}, and the singletons. The master neighbourhood is the whole set, which is nonempty and is a neighbourhood. Nested-or-disjointness is the stem comparison lemma, and every neighbourhood is contained in the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.flat_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.flat_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.stemMem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.stemNOD

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Exercise 1.15 — the stem domain.** `𝒟 = {ℕ, {0,1}} ∪ {{n}}`. -/
def stem : NeighborhoodSystem ℕ :=
  ofNestedOrDisjoint stemMem Set.univ Set.univ_nonempty
    (Or.inl rfl) stemNOD (fun _ => Set.subset_univ _)

end DomainTheory.NeighbourhoodSystems.Exercise115
