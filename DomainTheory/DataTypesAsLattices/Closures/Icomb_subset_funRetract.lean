module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_1

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































/-- **Scott 1976, (5.1).** Every set is below its graph, so `fun` is a closure. -/
theorem Icomb_subset_funRetract : Icomb ⊆ funRetract := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  exact ⟨n, m, rfl, eq_5_1 (e n) hm⟩

end DomainTheory.DataTypesAsLattices
