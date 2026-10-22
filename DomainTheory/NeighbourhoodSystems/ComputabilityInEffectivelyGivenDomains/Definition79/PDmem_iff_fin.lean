module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79.mem_PDunion

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Definition 7.9 — Scott's `⋃_{i<n}` form.** The neighbourhood family of `ℙ𝒟`, written with
a finite sequence `X : Fin n → 𝒟` exactly as Scott displays it: `W = ⋃_{i<n} ↓Xᵢ` with each
`Xᵢ ∈ 𝒟`. Equivalent to the `List` form via `List.ofFn` / `List.get`. -/
theorem PDmem_iff_fin {W : Set (Set α)} :
    V.PDmem W ↔ ∃ (n : ℕ) (X : Fin n → Set α),
      (∀ i, V.mem (X i)) ∧ W = ⋃ i, V.upSet (X i) := by
  constructor
  · rintro ⟨L, hL, rfl⟩
    refine ⟨L.length, L.get, fun i => hL _ (L.get_mem i), ?_⟩
    ext z
    rw [mem_PDunion, Set.mem_iUnion]
    constructor
    · rintro ⟨X, hX, hz⟩
      obtain ⟨i, rfl⟩ := List.get_of_mem hX
      exact ⟨i, hz⟩
    · rintro ⟨i, hz⟩
      exact ⟨L.get i, L.get_mem i, hz⟩
  · rintro ⟨n, X, hX, rfl⟩
    refine ⟨List.ofFn X, ?_, ?_⟩
    · intro Y hY
      obtain ⟨i, rfl⟩ := Set.mem_range.mp (List.mem_ofFn.mp hY)
      exact hX i
    · ext z
      rw [Set.mem_iUnion, mem_PDunion]
      constructor
      · rintro ⟨i, hz⟩
        exact ⟨X i, List.mem_ofFn.mpr (Set.mem_range.mpr ⟨i, rfl⟩), hz⟩
      · rintro ⟨Y, hY, hz⟩
        obtain ⟨i, rfl⟩ := Set.mem_range.mp (List.mem_ofFn.mp hY)
        exact ⟨i, hz⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
