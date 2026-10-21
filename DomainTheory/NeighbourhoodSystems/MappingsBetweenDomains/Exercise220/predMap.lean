/-ai
Predecessor on the powerset domain is the approximable map relating neighbourhoods X and Z when the complement of Z is contained in the predecessor of the complement of X. The master neighbourhoods are related because the complement of the universe is empty. The intersection law intersects the output neighbourhoods, using that the complement of an intersection is a union. A larger output has a smaller complement and a sharper input has a larger complement, and the predecessor of sets preserves that inclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet_inter_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_toSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.predSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_predSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.predSet_mono

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Exercise 2.20 — `x − 1` is approximable.** `X f Z ↔ Zᶜ ⊆ (Xᶜ − 1)`. -/
def predMap : ApproximableMap powerSet powerSet where
  rel X Z := powerSet.mem X ∧ powerSet.mem Z ∧ Zᶜ ⊆ predSet Xᶜ
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := by
    refine ⟨powerSet.master_mem, powerSet.master_mem, ?_⟩
    rw [powerSet_master, Set.compl_univ]; exact Set.empty_subset _
  inter_right := by
    rintro X Z Z' ⟨hX, hZ, hsub⟩ ⟨_, hZ', hsub'⟩
    refine ⟨hX, powerSet_inter_mem hZ hZ', ?_⟩
    rw [Set.compl_inter]; exact Set.union_subset hsub hsub'
  mono := by
    rintro X X' Z Z' ⟨_, _, hsub⟩ hX'X hZZ' hX' hZ'
    refine ⟨hX', hZ', ?_⟩
    exact (Set.compl_subset_compl.mpr hZZ').trans
      (hsub.trans (predSet_mono (Set.compl_subset_compl.mpr hX'X)))

end DomainTheory.NeighbourhoodSystems.Exercise220
