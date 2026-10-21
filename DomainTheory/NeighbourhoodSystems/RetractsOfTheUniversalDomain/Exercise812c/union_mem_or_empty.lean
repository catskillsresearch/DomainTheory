/-ai
If X and Y are each empty or a neighbourhood of a positive difference-closed system, then their union is empty or a neighbourhood.

If either set is empty, the union is the other set. If both are neighbourhoods, both lie under the master. If the master minus X is empty, then X is the master and the union is the master, and the same holds with Y in place of X. Otherwise both complements are neighbourhoods. The union identity rewrites the union as the master minus the intersection of the two complements. That intersection is empty, in which case the difference is the master, or nonempty, in which case positivity makes the intersection a neighbourhood and difference-closure makes the difference a neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.DiffClosed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_eq_master_diff_inter_compl

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **Union-closure from `IsPositive` + `DiffClosed` alone**: if `X` and `Y` are each mem-or-∅ in a
Positive, difference-closed `D`, so is `X ∪ Y`. -/
theorem union_mem_or_empty {γ : Type*} {D : NeighborhoodSystem γ} (hpos : D.IsPositive)
    (hdiff : D.DiffClosed) {X Y : Set γ} (hX : X = ∅ ∨ D.mem X) (hY : Y = ∅ ∨ D.mem Y) :
    X ∪ Y = ∅ ∨ D.mem (X ∪ Y) := by
  rcases hX with rfl | hX
  · simpa using hY
  · rcases hY with rfl | hY
    · simpa using Or.inr hX
    · set M := D.master with hMdef
      have hXM : X ⊆ M := D.sub_master hX
      have hYM : Y ⊆ M := D.sub_master hY
      rcases hdiff D.master_mem hX with hMX0 | hMXm
      · refine Or.inr ?_
        have hXeqM : X = M := Set.Subset.antisymm hXM (Set.sdiff_eq_empty.mp hMX0)
        rw [Set.Subset.antisymm (Set.union_subset hXM hYM) (hXeqM ▸ Set.subset_union_left)]
        exact D.master_mem
      · rcases hdiff D.master_mem hY with hMY0 | hMYm
        · refine Or.inr ?_
          have hYeqM : Y = M := Set.Subset.antisymm hYM (Set.sdiff_eq_empty.mp hMY0)
          rw [Set.Subset.antisymm (Set.union_subset hXM hYM) (hYeqM ▸ Set.subset_union_right)]
          exact D.master_mem
        · rw [union_eq_master_diff_inter_compl M X Y hXM hYM]
          rcases Set.eq_empty_or_nonempty ((M \ X) ∩ (M \ Y)) with hcap0 | hcapne
          · rw [hcap0, Set.sdiff_empty]; exact Or.inr D.master_mem
          · exact hdiff D.master_mem ((hpos hMXm hMYm).mpr hcapne)

end DomainTheory.NeighbourhoodSystems
