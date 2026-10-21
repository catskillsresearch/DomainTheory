/-ai
This file gathers and re-exports the computable presentation of U used for the master-neighbourhood facts of Exercise 8.12(g)(1)(a).
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation

@[expose] public section

/-!
# Exercise 8.12(g)(1)(a) — the `U`-side small assembly prerequisites

Two small facts `effectiveIso812d` (`Exercise812d.lean`) needs beyond `(c)`/`(d)`/`(e)`/`(f)`'s own
headline lemmas, for the `U` side: `U.master.Nonempty` (`hD₀mne`) and `UX 0 = U.master` (`hX0`).

Both are short and mechanical, reusing existing machinery with no new mathematical content:
`U.master.Nonempty` is immediate from `U.master = Set.Ico 0 1`; `UX_zero` unfolds `UX_eq` at `n = 0`
(`decodeQPairList 0 = []` via `decodeList_zero`), so `canonList` hits its own empty-input fallback
branch (`canonList_eq_of_filter_eq_nil`), landing on the same `[(0,1)] ↦ U.master` computation
`U_mem_presentedIntervals_canonList` already performs inline.
-/

namespace DomainTheory.NeighbourhoodSystems

end DomainTheory.NeighbourhoodSystems
