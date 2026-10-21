/-ai
The difference of two U-neighbourhoods is presentable if and only if it is nonempty.

A presenting index is a genuine neighbourhood, hence nonempty. Conversely the difference is empty or a neighbourhood; emptiness contradicts the hypothesis, and a neighbourhood is hit by the presentation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.U_diff_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **Scott's consistency condition for `\` reduces to non-emptiness**, exactly mirroring
`U_cons_iff_nonempty_inter`: `U_diff_mem` (`Exercise812c.lean`) shows `UX n \ UX m` is always either
empty or a genuine `U`-neighbourhood, and every `UX k` is non-empty (`U.mem` forces
`Set.Nonempty`), so "presentable" and "non-empty" coincide. -/
theorem U_diff_iff_nonempty (n m : ℕ) :
    (∃ k, UX k = UX n \ UX m) ↔ (UX n \ UX m).Nonempty := by
  constructor
  · rintro ⟨k, hk⟩
    rw [← hk]; exact (U_mem_UX k).2.1
  · intro hne
    rcases U_diff_mem (U_mem_UX n) (U_mem_UX m) with hempty | hmem
    · exact absurd hempty hne.ne_empty
    · exact U_surj_UX hmem

end DomainTheory.NeighbourhoodSystems
