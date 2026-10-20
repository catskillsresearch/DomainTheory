module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem111
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.prefixSeq
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.prefixSeq_length
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.prefixSeq_mono
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.branchSeq

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise113

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

theorem branchSeq_mono (p : ℕ → Bool) : Monotone (branchSeq p) := by
  intro n m h
  exact (sigmaBot_le_iff (prefixSeq p n) (prefixSeq p m)).mpr (prefixSeq_mono p h)

end DomainTheory.NeighbourhoodSystems.Exercise113
