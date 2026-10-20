module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.boool_expansive

@[expose] public section


namespace DomainTheory.DataTypesAsLattices



































theorem Icomb_subset_boool : Icomb ⊆ boool := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  exact ⟨n, m, rfl, boool_expansive (e n) hm⟩

end DomainTheory.DataTypesAsLattices
