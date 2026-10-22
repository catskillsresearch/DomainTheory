/-ai
Exercise 1.12 is the neighbourhood system of final segments of the natural numbers. It is obtained from the nested-or-disjoint construction, with neighbourhoods the tails and master neighbourhood the tail of zero, witnessed as nonempty by zero and equal to that tail. Any two tails are nested or disjoint, and every tail is contained in the tail of zero because zero is at most the tail's index.
ai-/
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
