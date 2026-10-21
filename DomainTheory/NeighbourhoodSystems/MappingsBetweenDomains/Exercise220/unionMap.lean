/-ai
Union on the powerset domain is the approximable map of two variables that relates neighbourhoods X, Y, and Z when the intersection of X and Y is contained in Z. The master neighbourhoods are related because the intersection of the universe with itself is contained in the universe. The intersection law intersects the two output neighbourhoods. Monotonicity composes the intersection of the sharper input inclusions with the output inclusion.
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
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_predSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Exercise 2.20 — `x ∪ y` is approximable (two variables).** `X, Y f Z ↔ X ∩ Y ⊆ Z`
(`(Xᶜ ∪ Yᶜ)ᶜ = X ∩ Y`). -/
def unionMap : ApproximableMap₂ powerSet powerSet powerSet where
  rel X Y Z := powerSet.mem X ∧ powerSet.mem Y ∧ powerSet.mem Z ∧ X ∩ Y ⊆ Z
  rel_dom₀ h := h.1
  rel_dom₁ h := h.2.1
  rel_cod h := h.2.2.1
  master_rel := ⟨powerSet.master_mem, powerSet.master_mem, powerSet.master_mem, Set.inter_subset_left⟩
  inter_right := by
    rintro X Y Z Z' ⟨hX, hY, hZ, hsub⟩ ⟨_, _, hZ', hsub'⟩
    exact ⟨hX, hY, powerSet_inter_mem hZ hZ', Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' Y Y' Z Z' ⟨_, _, _, hsub⟩ hX'X hY'Y hZZ' hX' hY' hZ'
    exact ⟨hX', hY', hZ', (Set.inter_subset_inter hX'X hY'Y).trans (hsub.trans hZZ')⟩

end DomainTheory.NeighbourhoodSystems.Exercise220
