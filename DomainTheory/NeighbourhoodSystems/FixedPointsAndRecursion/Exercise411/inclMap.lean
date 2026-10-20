module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The inclusion `𝒟ₐ → 𝒟` as an approximable map: an `a`-neighbourhood `X` relates to any larger
`𝒟`-neighbourhood `Y ⊇ X`. Its elementwise action is `embed a` (`inclMap_toElementMap`). -/
def inclMap (a : V.Element) : ApproximableMap (relSystem a) V where
  rel X Y := a.mem X ∧ V.mem Y ∧ X ⊆ Y
  rel_dom := fun h => h.1
  rel_cod := fun h => h.2.1
  master_rel := ⟨a.master_mem, V.master_mem, subset_rfl⟩
  inter_right := by
    rintro X Y Y' ⟨haX, hVY, hXY⟩ ⟨_, hVY', hXY'⟩
    exact ⟨haX, V.inter_mem hVY hVY' (a.sub haX) (Set.subset_inter hXY hXY'),
      Set.subset_inter hXY hXY'⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hXY⟩ hX'X hYY' haX' hVY'
    exact ⟨haX', hVY', (hX'X.trans hXY).trans hYY'⟩

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
