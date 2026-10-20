module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)















/-- **Part 6c's headline result.** `genAtom`-emptiness (for the reindexed enumeration `e P`, at any
sign sequence `δ` and depth `n`) reduces to `DAtom (P0 P)`-emptiness at the `posnegList`
accumulator — which Part 5's `DAtom_recDecidable (P0 P)` already decides, in the codes of *any*
list representing `(posnegList δ n).1`/`.2`. What remains for Part 6e is exactly to realize
`posnegList δ n`'s two components as *codes*, primitively in `n` and a code for `δ`'s first `n`
bits — composing that with `DAtom_recDecidable (P0 P)`'s extracted decider then decides
`genAtom`-emptiness outright, with no need to redo any of Part 5's meet-fold machinery. -/
theorem genAtom_empty_iff (δ : ℕ → Bool) (n : ℕ) :
    genAtom (idxSet (e P)) Set.univ δ n = ∅ ↔
      DAtom (P0 P) (posnegList δ n).1 (posnegList δ n).2 = ∅ := by
  rw [genAtom_eq_DAtom]

end DomainTheory.NeighbourhoodSystems
