/-ai
If n is at most m, then the length-n prefix of a path is a prefix of the length-m prefix.

The proof inducts along the inequality. The base case is reflexivity of the prefix relation. The successor step composes the inductive prefix with the one-step extension of the prefix.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem111
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.prefixSeq
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.prefixSeq_length
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.prefixSeq_prefix_succ

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise113

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

theorem prefixSeq_mono (p : ℕ → Bool) {n m : ℕ} (h : n ≤ m) :
    prefixSeq p n <+: prefixSeq p m := by
  induction m, h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ k _ ih => exact ih.trans (prefixSeq_prefix_succ p k)

end DomainTheory.NeighbourhoodSystems.Exercise113
