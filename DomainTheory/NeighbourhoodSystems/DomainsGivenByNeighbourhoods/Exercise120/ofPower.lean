/-ai
The filter of the original system corresponding to a filter of the power system consists of the neighbourhoods whose up-sets belong to that filter. A subset of such a neighbourhood is a neighbourhood. The master belongs because its up-set is the master of the power system. If the up-sets of two neighbourhoods belong to the filter, so does their intersection, which is the up-set of the intersection; a consistency witness for that up-set is a neighbourhood contained in both factors, so the intersection is a neighbourhood of the original system. A larger neighbourhood is admitted because containment of neighbourhoods yields containment of their up-sets.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.upSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.mem_upSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.upSet_inter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.upSet_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.powerSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.powerSystem_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The element of `|𝒟|` corresponding to `y ∈ |𝒟'|`: the filter `{W ∣ ↑W ∈ y}`. -/
def ofPower (y : V.powerSystem.Element) : V.Element where
  mem W := V.mem W ∧ y.mem (V.upSet W)
  sub h := h.1
  master_mem := ⟨V.master_mem, y.master_mem⟩
  inter_mem := by
    rintro X Y ⟨hX, hyX⟩ ⟨hY, hyY⟩
    have hyInter : y.mem (V.upSet X ∩ V.upSet Y) := y.inter_mem hyX hyY
    rw [V.upSet_inter] at hyInter
    obtain ⟨W, hW, hWeq⟩ := y.sub hyInter
    have hWin : W ∈ V.upSet (X ∩ Y) := by rw [hWeq]; exact ⟨hW, subset_rfl⟩
    exact ⟨V.inter_mem hX hY hW hWin.2, hyInter⟩
  up_mem := by
    rintro X Y ⟨hX, hyX⟩ hY hXY
    exact ⟨hY, y.up_mem hyX ⟨Y, hY, rfl⟩ ((V.upSet_subset_iff hX).mpr hXY)⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
