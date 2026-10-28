module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb_more
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_Vcomb
public import DomainTheory.DataTypesAsLattices.Closures.theorem_5_5_more
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Graph.funOf

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem theorem_5_5.universe :
    Closure Vcomb ∧ ∀ a, Closure a ↔ typed a Vcomb :=
  ⟨⟨⟨Icomb_subset_Vcomb, Vcomb.isRetract⟩⟩,
    fun a => (theorem_5_5.iff a).trans ⟨Eq.symm, Eq.symm⟩⟩

end DomainTheory.DataTypesAsLattices
