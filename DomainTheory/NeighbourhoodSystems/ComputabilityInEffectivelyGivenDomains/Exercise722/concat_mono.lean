/-ai
Concatenation of languages is monotone in both arguments.

A witnessing split of a word in the smaller concatenation remains a witnessing split after the two inclusions.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.InS
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.mem_concat

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap

/-- Concatenation is monotone in both arguments. -/
theorem concat_mono {X X' Y Y' : Set (List Bool)} (hX : X ⊆ X') (hY : Y ⊆ Y') :
    concat X Y ⊆ concat X' Y' := by
  rintro w ⟨a, ha, b, hb, rfl⟩; exact ⟨a, hX ha, b, hY hb, rfl⟩

end Exercise722

end DomainTheory.NeighbourhoodSystems
