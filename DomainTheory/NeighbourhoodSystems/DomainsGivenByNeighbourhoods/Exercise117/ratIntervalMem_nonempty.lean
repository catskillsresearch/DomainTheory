module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise117.ratIntervalMem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace RatInterval

open NeighborhoodSystem

/-- Every neighbourhood is non-empty (`Δ`, or `Ioo a b` with `a < b`). -/
theorem ratIntervalMem_nonempty {X : Set ℝ} (hX : ratIntervalMem X) : X.Nonempty := by
  rcases hX with rfl | ⟨a, b, hab, rfl⟩
  · exact ⟨0, Set.mem_univ 0⟩
  · rw [Set.nonempty_Ioo]; exact_mod_cast hab

end RatInterval

end DomainTheory.NeighbourhoodSystems
