module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.tail
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.mem_tail
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.tail_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.nestedOrDisjoint

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Exercise 1.12.** The final-segment neighbourhood system on `ℕ` (master `Δ = tail 0 = ℕ`). -/
def neighborhoodSystem : NeighborhoodSystem ℕ :=
  ofNestedOrDisjoint mem (tail 0) ⟨0, Nat.zero_le 0⟩ ⟨0, rfl⟩ nestedOrDisjoint
    (fun {X} hX => by obtain ⟨n, rfl⟩ := hX; exact tail_subset_iff.mpr (Nat.zero_le n))

end DomainTheory.NeighbourhoodSystems.Exercise112
