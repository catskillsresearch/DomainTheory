module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.DAtom_eq_empty_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace inter

open NeighborhoodSystem

/-- **`A ∩ (M \ Z) = A \ Z` whenever `A ⊆ M`**: needed to turn a `genAtom`-style "intersect with
`M \ Z`" step into a literal `A \ Z` once `A` is known to already lie inside `M`. Generic set-theory
fact, used by 8.12(c)(vi)(5)(b)'s `genAtom.combinedX_succ_eq` below. -/
theorem diff_eq_diff_of_subset {γ : Type*} {A M Z : Set γ} (h : A ⊆ M) :
    A ∩ (M \ Z) = A \ Z := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_sdiff]
  constructor
  · rintro ⟨hxA, -, hxZ⟩; exact ⟨hxA, hxZ⟩
  · rintro ⟨hxA, hxZ⟩; exact ⟨hxA, h hxA, hxZ⟩

end inter
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace inter

open NeighborhoodSystem

theorem diff_self_eq_empty {γ : Type*} (P Q : Set γ) : (P ∩ Q) ∩ (P \ Q) = ∅ := by
  ext x; simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]; tauto

end inter
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace inter

open NeighborhoodSystem

theorem mem_or_empty {γ : Type*} {D : NeighborhoodSystem γ} (hpos : D.IsPositive)
    {A B : Set γ} (hA : A = ∅ ∨ D.mem A) (hB : D.mem B) : A ∩ B = ∅ ∨ D.mem (A ∩ B) := by
  rcases hA with rfl | hA
  · exact Or.inl (Set.empty_inter B)
  · rcases Set.eq_empty_or_nonempty (A ∩ B) with h | h
    · exact Or.inl h
    · exact Or.inr ((hpos hA hB).mpr h)

end inter
end DomainTheory.NeighbourhoodSystems
