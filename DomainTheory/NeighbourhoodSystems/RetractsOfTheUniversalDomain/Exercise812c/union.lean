module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_disjoint_YseqCode_of_posTwin_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_succ_true
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.hcoreIdxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.transfer_dir_idxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.DAtom_eq_empty_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace union

open NeighborhoodSystem

theorem eq_master_diff_inter_compl {γ : Type*} (M X Y : Set γ) (hX : X ⊆ M) (hY : Y ⊆ M) :
    X ∪ Y = M \ ((M \ X) ∩ (M \ Y)) := by
  ext x
  have hXx : x ∈ X → x ∈ M := @hX x
  have hYx : x ∈ Y → x ∈ M := @hY x
  simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]
  tauto

end union
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace union

open NeighborhoodSystem

/-- **Union-closure from `IsPositive` + `DiffClosed` alone**: if `X` and `Y` are each mem-or-∅ in a
Positive, difference-closed `D`, so is `X ∪ Y`. -/
theorem mem_or_empty {γ : Type*} {D : NeighborhoodSystem γ} (hpos : D.IsPositive)
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
        · rw [union.eq_master_diff_inter_compl M X Y hXM hYM]
          rcases Set.eq_empty_or_nonempty ((M \ X) ∩ (M \ Y)) with hcap0 | hcapne
          · rw [hcap0, Set.sdiff_empty]; exact Or.inr D.master_mem
          · exact hdiff D.master_mem ((hpos hMXm hMYm).mpr hcapne)

end union
end DomainTheory.NeighbourhoodSystems
