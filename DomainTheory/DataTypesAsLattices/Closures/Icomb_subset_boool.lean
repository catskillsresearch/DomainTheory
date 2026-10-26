
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.boool
@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Icomb_subset_boool : Icomb ⊆ boool := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  exact ⟨n, m, rfl, boool.expansive (e n) hm⟩

/-- **Scott 1976, (5.3).** `boool` is a closure. -/
theorem boool.isClosure : Closure boool :=
  ⟨⟨Icomb_subset_boool, boool.isRetract⟩⟩

end DomainTheory.DataTypesAsLattices
