module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **A list all of whose pairs are already non-degenerate is empty iff it presents `∅`** (unlike
an arbitrary presenting list, where individually-degenerate pairs could make this fail). -/
theorem presentedIntervals_eq_empty_iff_of_forall_lt {L' : List (ℚ × ℚ)}
    (hpos : ∀ p ∈ L', p.1 < p.2) : presentedIntervals L' = ∅ ↔ L' = [] := by
  constructor
  · intro h
    rcases L' with _ | ⟨a, l⟩
    · rfl
    · exact absurd h (Set.Nonempty.ne_empty ⟨a.1, mem_presentedIntervals.mpr
        ⟨a, List.mem_cons.mpr (Or.inl rfl), le_refl _,
          hpos a (List.mem_cons.mpr (Or.inl rfl))⟩⟩)
  · rintro rfl; exact presentedIntervals_nil

end DomainTheory.NeighbourhoodSystems
