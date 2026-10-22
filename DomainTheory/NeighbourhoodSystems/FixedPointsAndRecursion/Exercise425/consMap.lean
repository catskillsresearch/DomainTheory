module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.shift
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.mem_tail
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.shift_mono
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.memC1
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.memC1_univ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.memC1_shift
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.C1
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.C1_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.C1_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise425

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- **Exercise 4.25 — the successor `x ↦ 1x`** (analogous to the two successors of `C`). The
approximable map prepending a `1`, i.e. shifting the length: `X (1x) Y ↔ shift X ⊆ Y`. -/
def consMap : ApproximableMap C1 C1 where
  rel X Y := memC1 X ∧ memC1 Y ∧ shift X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨memC1_univ, memC1_univ, Set.subset_univ _⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hsub⟩ ⟨_, hY', hsub'⟩
    have hsubInter : shift X ⊆ Y ∩ Y' := Set.subset_inter hsub hsub'
    exact ⟨hX, C1.inter_mem hY hY' (memC1_shift hX) hsubInter, hsubInter⟩
  mono := by
    rintro X X' Y Y' ⟨hX, hY, hsub⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (shift_mono hX'X).trans (hsub.trans hYY')⟩

end DomainTheory.NeighbourhoodSystems.Exercise425
