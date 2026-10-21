/-ai
The typical Π₁¹ set is a Π₁¹ set.

A set is Π₁¹ when it is the set of x such that for every y there is a z with h(x)(y)(z) equal to {0}, for some Scott-continuous h. The identity is Scott continuous and reproduces the defining condition of the typical set.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


theorem typicalPi11_isPi11 : IsPi11 typicalPi11 :=
  ⟨fun u => u, id_isScottContinuous, rfl⟩

end DomainTheory.DataTypesAsLattices
