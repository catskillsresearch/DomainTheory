module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

theorem pair_lt_succ_sq (x y : ℕ) : Nat.pair x y < (max x y + 1) * (max x y + 1) := by
  have hm : ∀ z : ℕ, (z + 1) * (z + 1) = z * z + 2 * z + 1 := fun z => by
    rw [Nat.succ_mul, Nat.mul_succ]; omega
  unfold Nat.pair
  rcases lt_or_ge x y with h | h
  · rw [ite_eq_left h, show max x y = y by omega, hm]; omega
  · rw [ite_eq_right (by omega), show max x y = x by omega, hm]; omega

end Proposition77

end DomainTheory.NeighbourhoodSystems
