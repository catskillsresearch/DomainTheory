module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

theorem union_eq_master_diff_inter_compl {γ : Type*} (M X Y : Set γ) (hX : X ⊆ M) (hY : Y ⊆ M) :
    X ∪ Y = M \ ((M \ X) ∩ (M \ Y)) := by
  ext x
  have hXx : x ∈ X → x ∈ M := @hX x
  have hYx : x ∈ Y → x ∈ M := @hY x
  simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]
  tauto

end DomainTheory.NeighbourhoodSystems
