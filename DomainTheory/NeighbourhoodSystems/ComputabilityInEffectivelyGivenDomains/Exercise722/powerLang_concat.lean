/-ai
The concatenation of a power language with itself is contained in the power language.

A split into an m-fold repetition and an n-fold repetition is the repetition of count m plus n, by the addition law for repeated words.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap


theorem powerLang_concat (w : List Bool) :
    concat (powerLang w) (powerLang w) ⊆ powerLang w := by
  rintro u ⟨a, ⟨m, hm⟩, b, ⟨n, hn⟩, rfl⟩
  exact ⟨m + n, by rw [repeatWord_add, hm, hn]⟩

end Exercise722
end DomainTheory.NeighbourhoodSystems
