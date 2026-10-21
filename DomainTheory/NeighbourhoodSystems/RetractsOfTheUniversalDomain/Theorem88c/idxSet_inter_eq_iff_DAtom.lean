/-ai
For any computable presentation, the index sets of i and j meet in the index set of k if and only if the neighbourhood at k refines both the neighbourhood at i and the neighbourhood at j, and the D-atom on the lists [i, j] and [k] is empty.

The positive part of [i, j] is the intersection of the two index sets, so the D-atom is that intersection with the index set of k removed, and the atom is empty exactly when the intersection is contained in the index set of k. If the index sets are equal, each factor of the intersection gives an inclusion of index sets, which the inclusion rule turns into the two neighbourhood inclusions, and the containment half of the equality gives emptiness of the atom. Conversely, emptiness gives one inclusion of index sets, and the two neighbourhood inclusions give the other by the inclusion rule.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **`idxSet`-intersection, characterized by a single `DAtom` emptiness query.** For *any*
computable presentation `Q`, `idxSet Q.X i ∩ idxSet Q.X j = idxSet Q.X k` iff `Q.X k` refines both
`Q.X i` and `Q.X j` (Scott's own decidable inclusion) *and* the depth-2 atom `DAtom Q [i,j] [k]`
(positive constraints `{i,j}`, negative constraint `{k}`) is empty. The three pieces are each
decidable (`incl_computable` used twice, `DAtom_recDecidable` at a fixed 2-element/1-element list
pair), so this is
the bridge that lets Part 5's `DAtom` apparatus decide `idxSet`-level *equations*, not just
emptiness. -/
theorem idxSet_inter_eq_iff_DAtom {β : Type*} {V : NeighborhoodSystem β}
    (Q : ComputablePresentation V) (i j k : ℕ) :
    idxSet Q.X i ∩ idxSet Q.X j = idxSet Q.X k ↔
      Q.X k ⊆ Q.X i ∧ Q.X k ⊆ Q.X j ∧ DAtom Q [i, j] [k] = ∅ := by
  have hDAtom_iff : DAtom Q [i, j] [k] = ∅ ↔ idxSet Q.X i ∩ idxSet Q.X j ⊆ idxSet Q.X k := by
    have hIPos : IPos Q [i, j] = idxSet Q.X i ∩ idxSet Q.X j := by
      rw [IPos_cons, IPos_cons, IPos_nil, Set.inter_univ]
    have hDAtom_eq : DAtom Q [i, j] [k] = (idxSet Q.X i ∩ idxSet Q.X j) \ idxSet Q.X k := by
      show IPos Q [i, j] ∩ {m | ∀ j' ∈ ([k] : List ℕ), m ∉ idxSet Q.X j'} = _
      rw [hIPos]
      ext m
      simp [Set.mem_sdiff]
    rw [hDAtom_eq, Set.sdiff_eq_empty]
  constructor
  · intro heq
    have h1 : idxSet Q.X k ⊆ idxSet Q.X i := by rw [← heq]; exact Set.inter_subset_left
    have h2 : idxSet Q.X k ⊆ idxSet Q.X j := by rw [← heq]; exact Set.inter_subset_right
    exact ⟨(idxSet_subset_iff Q.X k i).mp h1, (idxSet_subset_iff Q.X k j).mp h2,
      hDAtom_iff.mpr heq.subset⟩
  · rintro ⟨hki, hkj, hempty⟩
    exact Set.Subset.antisymm (hDAtom_iff.mp hempty)
      (Set.subset_inter ((idxSet_subset_iff Q.X k i).mpr hki) ((idxSet_subset_iff Q.X k j).mpr hkj))

end DomainTheory.NeighbourhoodSystems
