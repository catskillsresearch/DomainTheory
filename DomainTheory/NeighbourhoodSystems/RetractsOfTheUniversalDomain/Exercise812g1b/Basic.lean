/-ai
This file gathers and re-exports the primitive-recursive level-set development used for the master-neighbourhood facts of Exercise 8.12(g)(1)(b).
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec

@[expose] public section

/-!
# Exercise 8.12(g)(1)(b) — the `V`-side small assembly prerequisites

Two small facts `effectiveIso812d` (`Exercise812d.lean`) needs beyond `(c)`/`(d)`/`(e)`/`(f)`'s own
headline lemmas, for the `V` side: `V.master.Nonempty` (`hD₁mne`) and `VX 0 = V.master` (`hY0`).

Mirrors `Exercise812g1a.lean`'s `U`-side facts exactly, but along `V`'s bitmask representation:
`V.master.Nonempty` is immediate from `V.master = Set.univ`; `VX_zero` unfolds `canonIdx 0` — since
`Nat.unpair 0 = (0, 0)` and `levelSet 0 0 = ∅` (no bits set in `0`), `canonIdx` hits its own
empty-input fallback branch (`canonIdx_eq_master_of_empty`), landing on `VmasterIdx`, whose
`VX`-image is already known to be `V.master` (`VX_VmasterIdx`).
-/

namespace DomainTheory.NeighbourhoodSystems

end DomainTheory.NeighbourhoodSystems
