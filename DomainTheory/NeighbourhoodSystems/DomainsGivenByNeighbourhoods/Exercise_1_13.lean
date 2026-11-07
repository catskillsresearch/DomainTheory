module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.BranchSeq

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open DomainTheory.NeighbourhoodSystems.BranchSeq
open NeighborhoodSystem BitDom

/-- Scott's Exercise 1.13: each infinite branch through binary sequences is total. -/
theorem exercise_1_13 : ∀ p : ℕ → Bool, B.IsTotal (branch p) :=
  branch_isTotal

