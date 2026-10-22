module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise114.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise114.empty_not_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise114.mem_singleton

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise114

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **Exercise 1.14 (total elements).** The principal filter of a *singleton* `{n}` is a total
(maximal) element: any `y` it approximates approximates it back. (A `y ⊋ ↑{n}` would contain some
`W ∌ n`; then `{n} ∩ W = ∅ ∈ y ⊆ 𝒟`, impossible.) These are exactly the total elements. -/
theorem singleton_isTotal (n : ℕ) :
    neighborhoodSystem.IsTotal (neighborhoodSystem.principal (mem_singleton n)) := by
  intro y hy W hW
  have hn : y.mem {n} := hy {n} ⟨mem_singleton n, subset_rfl⟩
  refine ⟨y.sub hW, ?_⟩
  by_contra hc
  rw [Set.singleton_subset_iff] at hc
  have hempty : ({n} : Set ℕ) ∩ W = (∅ : Set ℕ) := by
    ext k
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨rfl, hk⟩
    exact hc hk
  have hi := y.inter_mem hn hW
  rw [hempty] at hi
  exact empty_not_mem (y.sub hi)

end DomainTheory.NeighbourhoodSystems.Exercise114
