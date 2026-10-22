module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.UnionClosed
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **A union of two genuine `U`-neighbourhoods is again genuine, unconditionally** — no
`NoMinimal`/`DiffClosed` detour needed for `U` specifically: `U.mem`'s three conjuncts (presentable,
non-empty, `⊆ [0,1)`) each transfer directly across `∪` (presentability via list `++`; non-emptiness
since one side alone is already non-empty; the subset bound is monotone in `∪`). -/
theorem U_union_UX_mem (n m : ℕ) : U.mem (UX n ∪ UX m) := by
  obtain ⟨⟨L1, hL1⟩, hne1, hsub1⟩ := U_mem_UX n
  obtain ⟨⟨L2, hL2⟩, -, hsub2⟩ := U_mem_UX m
  exact ⟨⟨L1 ++ L2, by rw [presentedIntervals_append, hL1, hL2]⟩,
    hne1.mono Set.subset_union_left, Set.union_subset hsub1 hsub2⟩

end DomainTheory.NeighbourhoodSystems
