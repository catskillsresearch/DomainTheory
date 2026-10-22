module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.flat_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.flat_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- Neighbourhoods of the stem domain: `Δ = ℕ`, the pair `{0,1}`, and all singletons. -/
def stemMem (X : Set ℕ) : Prop := X = Set.univ ∨ X = {0, 1} ∨ ∃ n, X = {n}

end DomainTheory.NeighbourhoodSystems.Exercise115
