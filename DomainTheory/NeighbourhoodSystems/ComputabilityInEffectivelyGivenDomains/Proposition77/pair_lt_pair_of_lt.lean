/-ai
If x is strictly below i and y is strictly below j, then the pair of x and y is strictly below the pair of i and j.

The pair of x and y is strictly below the square of one more than their maximum, and the square of the maximum of i and j is at most the pair of i and j. One more than the maximum of x and y is at most the maximum of i and j, by comparing with the larger of i and j, so the squares compare and the two bounds combine.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.pair_lt_succ_sq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.max_sq_le_pair

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

theorem pair_lt_pair_of_lt {x y i j : ℕ} (hx : x < i) (hy : y < j) :
    Nat.pair x y < Nat.pair i j := by
  have h1 : Nat.pair x y < (max x y + 1) * (max x y + 1) := pair_lt_succ_sq x y
  have h2 : max i j * max i j ≤ Nat.pair i j := max_sq_le_pair i j
  have h3 : max x y + 1 ≤ max i j := by
    rcases le_total x y with h | h
    · rw [max_eq_right h]; have := le_max_right i j; omega
    · rw [max_eq_left h]; have := le_max_left i j; omega
  have h4 : (max x y + 1) * (max x y + 1) ≤ max i j * max i j := Nat.mul_le_mul h3 h3
  omega

end Proposition77

end DomainTheory.NeighbourhoodSystems
