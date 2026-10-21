/-ai
For a computable presentation, the meet condition on indices n, m, and k holds if and only if the intersection of the n-th and m-th neighbourhoods equals the k-th neighbourhood.

If the meet condition holds, the k-th neighbourhood is contained in the intersection. That containment and the intersection law make the intersection a neighbourhood, so some enumerated neighbourhood equals it. The meet condition at that index places the intersection inside the k-th neighbourhood. Conversely, if the intersection equals the k-th neighbourhood, containment in the k-th neighbourhood is containment in both of the others.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.InclStructure
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.mem_toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toSystem_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {V : NeighborhoodSystem α}

/-- **The `MEET ↔ interEq` reduction.** On an effectively given system, Scott's `MEET(n, m, k)` is
equivalent to `Xₙ ∩ Xₘ = Xₖ`, so it is decidable by relation 7.1(i).

`⇐` is `Set.subset_inter_iff`. `⇒`: from `MEET` at `j = k` we get `Xₖ ⊆ Xₙ ∩ Xₘ`, so `Xₖ` witnesses
consistency of `(n, m)`; `inter_mem` then makes `Xₙ ∩ Xₘ` a neighbourhood, `surj` enumerates it as
some `Xₚ`, and `MEET` at `j = p` gives `Xₙ ∩ Xₘ = Xₚ ⊆ Xₖ`. -/
theorem meet_iff_interEq (P : ComputablePresentation V) (n m k : ℕ) :
    (∀ j, P.X j ⊆ P.X k ↔ (P.X j ⊆ P.X n ∧ P.X j ⊆ P.X m)) ↔ (P.X n ∩ P.X m = P.X k) := by
  constructor
  · intro h
    have hk : P.X k ⊆ P.X n ∩ P.X m :=
      Set.subset_inter ((h k).mp subset_rfl).1 ((h k).mp subset_rfl).2
    refine Set.Subset.antisymm ?_ hk
    have hmem : V.mem (P.X n ∩ P.X m) := V.inter_mem (P.mem_X n) (P.mem_X m) (P.mem_X k) hk
    obtain ⟨p, hp⟩ := P.surj hmem
    have hpk : P.X p ⊆ P.X k :=
      (h p).mpr (by rw [hp]; exact ⟨Set.inter_subset_left, Set.inter_subset_right⟩)
    exact hp ▸ hpk
  · intro h j
    rw [← h, Set.subset_inter_iff]

end DomainTheory.NeighbourhoodSystems.Exercise713
