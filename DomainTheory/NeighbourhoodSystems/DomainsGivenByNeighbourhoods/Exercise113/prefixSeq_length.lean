module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem111
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.prefixSeq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise113

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

@[simp] theorem prefixSeq_length (p : ℕ → Bool) (n : ℕ) : (prefixSeq p n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [prefixSeq, ih]

end DomainTheory.NeighbourhoodSystems.Exercise113
