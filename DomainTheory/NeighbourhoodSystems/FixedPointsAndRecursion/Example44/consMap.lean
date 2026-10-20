module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.prepend_mono
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.memC
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.C
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.C_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.C_master
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.memC_prepend

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example44

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB

/-- **Example 4.4 — the successors `x ↦ bx`.** The approximable map prepending the bit `b`:
`X (bx) Y ↔ bX ⊆ Y`. Approximable because `bX` is again a neighbourhood (`memC_prepend`) and
prepending is monotone. -/
def consMap (b : Bool) : ApproximableMap C C where
  rel X Y := memC X ∧ memC Y ∧ prepend [b] X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := by
    refine ⟨Or.inl ⟨[], cone_nil.symm⟩, Or.inl ⟨[], cone_nil.symm⟩, ?_⟩
    exact Set.subset_univ _
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hsub⟩ ⟨_, hY', hsub'⟩
    have hsubInter : prepend [b] X ⊆ Y ∩ Y' := Set.subset_inter hsub hsub'
    have hZ : memC (prepend [b] X) := memC_prepend [b] hX
    exact ⟨hX, C.inter_mem hY hY' hZ hsubInter, hsubInter⟩
  mono := by
    rintro X X' Y Y' ⟨hX, hY, hsub⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (prepend_mono [b] hX'X).trans (hsub.trans hYY')⟩

end DomainTheory.NeighbourhoodSystems.Example44
