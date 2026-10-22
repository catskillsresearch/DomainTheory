module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **`A ∩ (M \ Z) = A \ Z` whenever `A ⊆ M`**: needed to turn a `genAtom`-style "intersect with
`M \ Z`" step into a literal `A \ Z` once `A` is known to already lie inside `M`. Generic set-theory
fact, used by 8.12(c)(vi)(5)(b)'s `genAtom_combinedX_succ_eq` below. -/
theorem inter_diff_eq_diff_of_subset {γ : Type*} {A M Z : Set γ} (h : A ⊆ M) :
    A ∩ (M \ Z) = A \ Z := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_sdiff]
  constructor
  · rintro ⟨hxA, -, hxZ⟩; exact ⟨hxA, hxZ⟩
  · rintro ⟨hxA, hxZ⟩; exact ⟨hxA, h hxA, hxZ⟩

end DomainTheory.NeighbourhoodSystems
