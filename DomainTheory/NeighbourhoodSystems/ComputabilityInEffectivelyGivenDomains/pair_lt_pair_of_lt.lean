module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_reindexF
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber_reindexG

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

variable {V : NeighborhoodSystem α}

/-- `Nat.pair` is strictly monotone on strict componentwise order (local copy of the
`Proposition77` lemma to avoid the heavy import). -/
theorem pair_lt_pair_of_lt {x y i j : ℕ} (hx : x < i) (hy : y < j) :
    Nat.pair x y < Nat.pair i j := by
  have hms : ∀ z : ℕ, (z + 1) * (z + 1) = z * z + 2 * z + 1 := fun z => by
    rw [Nat.succ_mul, Nat.mul_succ]; omega
  have hlt : Nat.pair x y < (max x y + 1) * (max x y + 1) := by
    unfold Nat.pair
    rcases lt_or_ge x y with h | h
    · rw [ite_eq_left h, show max x y = y by omega, hms]; omega
    · rw [ite_eq_right (by omega), show max x y = x by omega, hms]; omega
  have hle : max i j * max i j ≤ Nat.pair i j := by
    unfold Nat.pair
    rcases lt_or_ge i j with h | h
    · rw [ite_eq_left h, show max i j = j by omega]; omega
    · rw [ite_eq_right (by omega), show max i j = i by omega]; omega
  have h3 : max x y + 1 ≤ max i j := by
    rcases le_total x y with h | h
    · rw [max_eq_right h]; have := le_max_right i j; omega
    · rw [max_eq_left h]; have := le_max_left i j; omega
  have h4 : (max x y + 1) * (max x y + 1) ≤ max i j * max i j := Nat.mul_le_mul h3 h3
  omega

end Exercise718

end DomainTheory.NeighbourhoodSystems
